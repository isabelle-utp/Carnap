{-#LANGUAGE RankNTypes, FlexibleContexts #-}

module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Data.Char (isSpace)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Data.Maybe (fromMaybe)
import Text.Parsec (parse, eof)
import Text.Parsec.Error (errorMessages, errorPos, showErrorMessages)
import Text.Parsec.Pos (sourceColumn)
import Control.Monad.State (State)

import Carnap.Calculi.NaturalDeduction.Syntax
    (NaturalDeductionCalc(..), Feedback(..), SupportsND)
import Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequence)
import Carnap.Calculi.Util
    (ProofErrorMessage(..), defaultRuntimeDeductionConfig)
import Carnap.Core.Data.Optics (PrismSubstitutionalVariable)
import Carnap.Core.Unification.Unification (MonadVar)
import Carnap.Languages.ClassicalSequent.Syntax (ClassicalSequentOver, Sequent, Sequentable)
import Carnap.Languages.PurePropositional.Logic (ofPropSys)
import Carnap.Languages.PureFirstOrder.Logic (ofFOLSys)
import Carnap.Languages.ModalPropositional.Logic (ofModalPropSys)
import Carnap.Languages.ModalFirstOrder.Logic (hardegreeMPLCalc)
import Carnap.Languages.PureSecondOrder.Logic (ofSecondOrderSys)
import Carnap.Languages.SetTheory.Logic (ofSetTheorySys)
import Carnap.Languages.HigherOrderArithmetic.Logic (ofHigherOrderArithmeticSys)
import Carnap.Languages.HOArithSum.Logic (ofHOArithSumSys)
import Carnap.Languages.DefiniteDescription.Logic.Gamut (ofDefiniteDescSys)

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["--list"]           -> printSystems
        [file]               -> processFile Nothing    file
        [defaultLogic, file] -> processFile (Just defaultLogic) file
        _                    -> usage >> exitFailure

usage :: IO ()
usage = do
    hPutStrLn stderr "Usage: carnap-check [<default-logic>] <file>"
    hPutStrLn stderr "       carnap-check --list"

processFile :: Maybe String -> FilePath -> IO ()
processFile cliDefault path = do
    src <- readFile path
    case parseFile src of
        Left err -> do
            hPutStrLn stderr err
            exitFailure
        Right blocks -> do
            ref <- newIORef (ProcState cliDefault 1 [])
            mapM_ (runBlock ref) blocks
            ProcState _ _ results <- readIORef ref
            summarize (reverse results)

--------------------------------------------------------------------------------
-- File parsing
--------------------------------------------------------------------------------

data Block = LogicDecl String
           | Lemma
                { lemName  :: Maybe String
                , lemLogic :: Maybe String
                , lemGoal  :: Maybe String
                , lemProof :: String
                , lemLine  :: Int
                }
    deriving Show

parseFile :: String -> Either String [Block]
parseFile src = go 1 (lines src) []
  where
    go _ []     acc = Right (reverse acc)
    go n (l:ls) acc
        | isBlank l || isLineComment l = go (n+1) ls acc
        | Just rest <- matchKeyword "logic" l =
            case strip rest of
                ""   -> Left $ lineErr n "expected logic name after 'logic'"
                name -> go (n+1) ls (LogicDecl name : acc)
        | Just rest <- matchKeyword "lemma" l =
            case parseLemmaHeader rest of
                Left msg -> Left $ lineErr n msg
                Right (mn, mlg, mgl) -> do
                    (body, ls', n') <- collectProof (n+1) ls
                    go n' ls' (Lemma mn mlg mgl body n : acc)
        | otherwise = Left $ lineErr n ("unexpected input: " ++ strip l)

matchKeyword :: String -> String -> Maybe String
matchKeyword kw line =
    let s = ltrim line
    in case splitAt (length kw) s of
           (w, rest)
               | w == kw && terminator rest -> Just rest
               | otherwise -> Nothing
  where
    terminator ""    = True
    terminator (c:_) = isSpace c || c == ':'

collectProof :: Int -> [String] -> Either String (String, [String], Int)
collectProof n [] = Left $ lineErr n "expected 'begin' but reached end of file"
collectProof n (l:ls)
    | isBlank l || isLineComment l = collectProof (n+1) ls
    | strip l == "begin"           = gather (n+1) ls []
    | otherwise = Left $ lineErr n ("expected 'begin' but found: " ++ strip l)
  where
    gather m [] _ = Left $ lineErr m "expected 'end' but reached end of file"
    gather m (x:xs) acc
        | strip x == "end" = Right (unlines (reverse acc), xs, m+1)
        | otherwise        = gather (m+1) xs (x : acc)

-- Parses the part of a `lemma ...` header that follows the keyword.
-- Input can be empty or any of:
--     Name
--     Name in Logic
--     Name: Goal
--     Name in Logic: Goal
--     : Goal
--     in Logic
--     in Logic: Goal
parseLemmaHeader :: String -> Either String (Maybe String, Maybe String, Maybe String)
parseLemmaHeader raw = case ltrim raw of
    ""            -> Right (Nothing, Nothing, Nothing)
    s@(':':_)     -> do
        (lg, gl) <- parseAfterName s
        Right (Nothing, lg, gl)
    s -> case takeWord s of
        ("in", rest) -> do
            (lg, gl) <- parseInClause rest
            Right (Nothing, lg, gl)
        (nm,  rest) -> do
            (lg, gl) <- parseAfterName rest
            Right (Just nm, lg, gl)

-- After an optional name, we may see: nothing, `in Logic`, or `: Goal`
parseAfterName :: String -> Either String (Maybe String, Maybe String)
parseAfterName raw = case ltrim raw of
    ""      -> Right (Nothing, Nothing)
    ':':gl  -> Right (Nothing, nonEmpty (strip gl))
    s -> case takeWord s of
        ("in", rest) -> parseInClause rest
        _            -> Left $ "expected 'in' or ':' after lemma name, got: " ++ s

-- After `in`, we expect a logic name, then optionally `: Goal`
parseInClause :: String -> Either String (Maybe String, Maybe String)
parseInClause raw = case takeWord (ltrim raw) of
    ("", _)   -> Left "expected logic name after 'in'"
    (lg, rest) -> case ltrim rest of
        ""       -> Right (Just lg, Nothing)
        ':':gl   -> Right (Just lg, nonEmpty (strip gl))
        other    -> Left $ "expected ':' or end of line after logic name, got: " ++ other

takeWord :: String -> (String, String)
takeWord s = break (\c -> isSpace c || c == ':') s

nonEmpty :: String -> Maybe String
nonEmpty "" = Nothing
nonEmpty s  = Just s

isBlank :: String -> Bool
isBlank = all isSpace

isLineComment :: String -> Bool
isLineComment l = case ltrim l of
    '-':'-':_ -> True
    _         -> False

lineErr :: Int -> String -> String
lineErr n msg = "Line " ++ show n ++ ": " ++ msg

ltrim :: String -> String
ltrim = dropWhile isSpace

strip :: String -> String
strip = reverse . ltrim . reverse . ltrim

--------------------------------------------------------------------------------
-- Processing lemmas
--------------------------------------------------------------------------------

data ProcState = ProcState
    { currentLogic :: Maybe String
    , lemmaCounter :: Int
    , lemmaResults :: [LemmaOutcome]
    }

data LemmaOutcome = Proved | Mismatch | Failed
    deriving (Eq, Show)

runBlock :: IORef ProcState -> Block -> IO ()
runBlock ref (LogicDecl name) =
    modifyIORef' ref (\s -> s { currentLogic = Just name })
runBlock ref (Lemma mname mlogic mgoal body hdrLine) = do
    st <- readIORef ref
    let name  = fromMaybe (show (lemmaCounter st)) mname
        logic = mlogic <|> currentLogic st
    modifyIORef' ref (\s -> s { lemmaCounter = lemmaCounter s + 1 })
    case logic of
        Nothing -> do
            hPutStrLn stderr $ "lemma " ++ name ++ " (line " ++ show hdrLine
                            ++ "): no logic specified and no default available"
            hPutStrLn stderr "  pass a default on the command line or add a 'logic <name>' declaration"
            record ref Failed
        Just sys -> do
            outcome <- checkLemmaInSystem name sys mgoal body
            record ref outcome

record :: IORef ProcState -> LemmaOutcome -> IO ()
record ref o = modifyIORef' ref (\s -> s { lemmaResults = o : lemmaResults s })

checkLemmaInSystem :: String -> String -> Maybe String -> String -> IO LemmaOutcome
checkLemmaInSystem name sys mgoal proof =
    case dispatch of
        Nothing -> do
            hPutStrLn stderr $ "lemma " ++ name ++ ": unknown logic system '" ++ sys ++ "'"
            hPutStrLn stderr "  use --list to see available systems"
            return Failed
        Just act -> act
  where
    dispatch =
            (runCheck name sys mgoal proof `ofPropSys` sys)
        <|> (runCheck name sys mgoal proof `ofFOLSys` sys)
        <|> (runCheck name sys mgoal proof `ofModalPropSys` sys)
        <|> (if sys == "hardegreeMPL" then Just (runCheck name sys mgoal proof hardegreeMPLCalc) else Nothing)
        <|> (runCheck name sys mgoal proof `ofSecondOrderSys` sys)
        <|> (runCheck name sys mgoal proof `ofSetTheorySys` sys)
        <|> (runCheck name sys mgoal proof `ofHigherOrderArithmeticSys` sys)
        <|> (runCheck name sys mgoal proof `ofHOArithSumSys` sys)
        <|> (runCheck name sys mgoal proof `ofDefiniteDescSys` sys)

runCheck :: ( SupportsND r lex sem
            , Sequentable lex
            , PrismSubstitutionalVariable lex
            , MonadVar (ClassicalSequentOver lex) (State Int)
            , Show (ClassicalSequentOver lex (Sequent sem))
            )
         => String
         -> String
         -> Maybe String
         -> String
         -> NaturalDeductionCalc r lex sem
         -> IO LemmaOutcome
runCheck name sys mgoal proof calc = do
    let trimmedProof = strip proof
        ded = ndParseProof calc defaultRuntimeDeductionConfig trimmedProof
        Feedback mseq ds = toDisplaySequence (ndProcessLine calc) ded
        errors = concatMap reportError (zip [1..] ds)
        prettySeq = ndNotation calc . show
    case mgoal of
        Nothing -> do
            mapM_ (hPutStrLn stderr . prefixed name) errors
            case mseq of
                Just sq -> do
                    putStrLn $ "lemma " ++ name ++ " (" ++ sys ++ "): " ++ prettySeq sq
                    return Proved
                Nothing -> do
                    hPutStrLn stderr $ "lemma " ++ name ++ " (" ++ sys ++ "): proof invalid"
                    return Failed
        Just goalText ->
            case parse (ndParseSeq calc <* eof) "" (convertTurnstile goalText) of
                Left pe -> do
                    hPutStrLn stderr $ "lemma " ++ name ++ ": could not parse goal '"
                                    ++ goalText ++ "': "
                                    ++ showErrorMessages "or" "unknown" "expecting" "unexpected" "end of input" (errorMessages pe)
                    return Failed
                Right goalSeq -> do
                    mapM_ (hPutStrLn stderr . prefixed name) errors
                    case mseq of
                        Just sq
                          | normalizeSeq (show sq) == normalizeSeq (show goalSeq) -> do
                                putStrLn $ "lemma " ++ name ++ " (" ++ sys ++ "): " ++ prettySeq sq
                                return Proved
                          | otherwise -> do
                                hPutStrLn stderr $ "lemma " ++ name ++ " (" ++ sys ++ "): proved the wrong goal"
                                hPutStrLn stderr $ "  expected: " ++ prettySeq goalSeq
                                hPutStrLn stderr $ "  proved:   " ++ prettySeq sq
                                return Mismatch
                        Nothing -> do
                            hPutStrLn stderr $ "lemma " ++ name ++ " (" ++ sys ++ "): proof invalid"
                            hPutStrLn stderr $ "  expected: " ++ prettySeq goalSeq
                            return Failed

prefixed :: String -> String -> String
prefixed name msg = "lemma " ++ name ++ ": " ++ msg

-- The empty antecedent renders as ⊤ when produced by the goal parser
-- (NilAntecedent) but as ∅ when produced as the lower sequent of a no-premise
-- rule (NilCedent).  These are semantically equivalent; canonicalize for
-- comparison.
normalizeSeq :: String -> String
normalizeSeq = go
  where go ('⊤':' ':'⊢':rest) = '∅' : ' ' : '⊢' : go rest
        go (c:cs) = c : go cs
        go []     = []

-- Rewrites `|-` to `⊢` so the user can type the sequent separator naturally
-- while the sequent parser (which accepts `⊢` or `:|-:`) still works.
convertTurnstile :: String -> String
convertTurnstile []           = []
convertTurnstile ('|':'-':xs) = '⊢' : convertTurnstile xs
convertTurnstile (c:xs)       = c   : convertTurnstile xs

--------------------------------------------------------------------------------
-- Reporting
--------------------------------------------------------------------------------

reportError :: (Int, Either (ProofErrorMessage lex) a) -> [String]
reportError (_, Right _)                 = []
reportError (_, Left (NoResult _))       = []
reportError (_, Left (NoParse err ln))   =
    ["Line " ++ show ln ++ ", column " ++ show (sourceColumn (errorPos err))
     ++ ": parse error: "
     ++ showErrorMessages "or" "unknown" "expecting" "unexpected" "end of input"
            (errorMessages err)]
reportError (_, Left (NoUnify _ ln))     =
    ["Line " ++ show ln ++ ": could not unify"]
reportError (_, Left (GenericError m ln)) =
    ["Line " ++ show ln ++ ": " ++ m]

summarize :: [LemmaOutcome] -> IO ()
summarize outcomes = do
    let total  = length outcomes
        proved = length (filter (== Proved) outcomes)
    putStrLn ""
    if total == 0
       then putStrLn "Summary: no lemmas found."
       else if proved == total
           then do putStrLn "Summary: all lemmas proved."
                   exitSuccess
           else do putStrLn $ "Summary: " ++ show proved ++ "/" ++ show total ++ " lemmas proved."
                   exitFailure

--------------------------------------------------------------------------------
-- System listing
--------------------------------------------------------------------------------

printSystems :: IO ()
printSystems = do
    putStrLn "Available systems:"
    putStrLn ""
    putStrLn "Propositional logic:"
    mapM_ (putStrLn . ("  " ++)) propSystems
    putStrLn ""
    putStrLn "First-order logic:"
    mapM_ (putStrLn . ("  " ++)) folSystems
    putStrLn ""
    putStrLn "Modal propositional logic:"
    mapM_ (putStrLn . ("  " ++)) modalPropSystems
    putStrLn ""
    putStrLn "Modal first-order logic:"
    mapM_ (putStrLn . ("  " ++)) modalFOLSystems
    putStrLn ""
    putStrLn "Second-order logic:"
    mapM_ (putStrLn . ("  " ++)) secondOrderSystems
    putStrLn ""
    putStrLn "Set theory:"
    mapM_ (putStrLn . ("  " ++)) setTheorySystems
    putStrLn ""
    putStrLn "Higher-order arithmetic:"
    mapM_ (putStrLn . ("  " ++)) hoArithSystems
    putStrLn ""
    putStrLn "Definite descriptions:"
    mapM_ (putStrLn . ("  " ++)) definiteDescSystems

propSystems :: [String]
propSystems =
    [ "LogicBookSD", "LogicBookSDPlus"
    , "allenSL", "allenSLPlus"
    , "arthurSL"
    , "belotSD", "belotSDPlus"
    , "bonevacSL"
    , "cortensSL"
    , "davisSL"
    , "ebelsDugganTFL"
    , "fosterAndLaursenTFL", "fosterAndLaursenTFL2019", "fosterAndLaursenTFLCore"
    , "gallowSL", "gallowSLPlus"
    , "gamutIPND", "gamutMPND", "gamutPND", "gamutPNDPlus"
    , "goldfarbPropND"
    , "gregorySD", "gregorySDE"
    , "hardegreeSL", "hardegreeSL2006"
    , "hausmanSL"
    , "howardSnyderSL"
    , "hurleySL"
    , "ichikawaJenkinsSL"
    , "landeProp"
    , "lemmonProp"
    , "magnusSL", "magnusSLPlus"
    , "montagueSC"
    , "prop", "propStrict", "propNonC", "propNL", "propNLStrict"
    , "thomasBolducAndZachTFL", "thomasBolducAndZachTFL2019", "thomasBolducAndZachTFLCore"
    , "tomassiPL"
    , "winklerTFL"
    , "zachPropEq"
    ]

folSystems :: [String]
folSystems =
    [ "LogicBookPD", "LogicBookPDE", "LogicBookPDEPlus", "LogicBookPDPlus"
    , "arthurQL"
    , "belotPD", "belotPDE", "belotPDEPlus", "belotPDPlus"
    , "bonevacQL"
    , "cortensQL"
    , "davisQL"
    , "ebelsDugganFOL"
    , "firstOrder", "firstOrderNonC"
    , "fosterAndLaursenFOL", "fosterAndLaursenFOL2019", "fosterAndLaursenFOLCore", "fosterAndLaursenFOLPlus2019"
    , "gallowPL", "gallowPLPlus"
    , "gamutND", "gamutNDPlus"
    , "goldfarbAltND", "goldfarbAltNDPlus", "goldfarbND", "goldfarbNDPlus"
    , "gregoryPD", "gregoryPDE"
    , "hardegreePL", "hardegreePL2006"
    , "hausmanPL"
    , "howardSnyderPL"
    , "hurleyPL"
    , "ichikawaJenkinsQL"
    , "landeQuant"
    , "lemmonQuant"
    , "magnusQL", "magnusQLPlus"
    , "montagueQC"
    , "thomasBolducAndZachFOL", "thomasBolducAndZachFOL2019"
    , "thomasBolducAndZachFOLCore", "thomasBolducAndZachFOLPlus2019"
    , "tomassiQL"
    , "winklerFOL"
    , "zachFOLEq"
    ]

modalPropSystems :: [String]
modalPropSystems =
    [ "hardegreeB"
    , "hardegreeD"
    , "hardegreeK"
    , "hardegreeL"
    , "hardegreeT"
    , "hardegreeWTL"
    , "hardegree4"
    , "hardegree5"
    ]

modalFOLSystems :: [String]
modalFOLSystems =
    [ "hardegreeMPL"
    ]

secondOrderSystems :: [String]
secondOrderSystems =
    [ "gamutNDSOL"
    , "polyadicSecondOrder"
    , "secondOrder"
    ]

setTheorySystems :: [String]
setTheorySystems =
    [ "elementarySetTheory"
    , "separativeSetTheory"
    ]

hoArithSystems :: [String]
hoArithSystems =
    [ "openLogicExHOArith"
    , "hoArithSumFL"
    ]

definiteDescSystems :: [String]
definiteDescSystems =
    [ "gamutNDDesc"
    ]
