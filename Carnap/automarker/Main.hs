{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}

module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr, readFile, writeFile)
import Control.Applicative ((<|>))
import Control.Monad (void, foldM)
import Data.Char (isSpace, isDigit, chr)
import Data.List (dropWhileEnd, isInfixOf, find, nub, intercalate)
import Data.Maybe (fromMaybe, isJust)
import Data.Aeson (FromJSON, ToJSON, decode)
import qualified Data.ByteString.Lazy as BL
import GHC.Generics (Generic)
import Text.Parsec hiding ((<|>), State)
import Text.Parsec.String (Parser)
import Text.Parsec.Error (errorMessages, errorPos, showErrorMessages)
import Text.Parsec.Pos (sourceColumn)
import Control.Monad.State (State)

-- Carnap Imports
import Carnap.Core.Data.Types (FixLang)
import Carnap.Calculi.NaturalDeduction.Syntax
    (NaturalDeductionCalc(..), Feedback(..), DeductionLine(..), SupportsND, justificationOf, depth, assertion)
import Carnap.Calculi.NaturalDeduction.Checker (toDisplaySequence, seqSubsetUnify)
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
import Carnap.Languages.Util.LanguageClasses (ParsableLex)

--------------------------------------------------------------------------------
-- Data Structures: Exam Schema & Partial Marking Rules
--------------------------------------------------------------------------------

data PartialRule
    = DeriveFact { factFormula :: String, factMarks :: Double }
    | ApplyRule  { ruleNames :: [String], ruleMarks :: Double }
    deriving (Show, Generic)

instance FromJSON PartialRule
instance ToJSON PartialRule

data QuestionType
    = ProofExercise
        { systemName   :: String
        , targetGoal   :: String
        , partialRules :: Maybe [PartialRule]
        }
    | TranslationChoice
        { systemName :: String
        , targetGoal :: String
        }
    | ExactMatch
        { expectedAnswer :: String }
    deriving (Show, Generic)

instance FromJSON QuestionType
instance ToJSON QuestionType

data QuestionSpec = QuestionSpec
    { qLabel :: String
    , qMarks :: Double
    , qType  :: QuestionType
    } deriving (Show, Generic)

instance FromJSON QuestionSpec
instance ToJSON QuestionSpec

data ExamSchema = ExamSchema
    { examTitle     :: String
    , defaultSystem :: String
    , questions     :: [QuestionSpec]
    } deriving (Show, Generic)

instance FromJSON ExamSchema
instance ToJSON ExamSchema

--------------------------------------------------------------------------------
-- Data Structures: Browser Submission Format
--------------------------------------------------------------------------------

data Submission = Submission
    { subTitle     :: String
    , subSavedOn   :: String
    , subExercises :: [Exercise]
    } deriving (Eq, Show)

data Exercise = Exercise
    { exLabel   :: String
    , exContent :: String
    } deriving (Eq, Show)

data ValidLine = ValidLine
    { lineNum       :: Int
    , lineFormula   :: String                  -- Decoded string for fallback matching & debug logging
    , lineRule      :: String                  -- Normalized rule string (e.g., "∨E")
    , lineDepth     :: Int                     -- Subproof depth
    } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Parsec Parser for JS-Downloaded Browser Submissions
--------------------------------------------------------------------------------

parseCarnapBrowserFile :: String -> Either ParseError Submission
parseCarnapBrowserFile = parse submissionParser ""

submissionParser :: Parser Submission
submissionParser = do
    title <- lineContent
    savedOn <- option "" (try savedOnLine)
    skipMany (char '-' <|> space)
    spaces
    exercises <- many exerciseParser
    eof
    return $ Submission (trim title) (trim savedOn) exercises

endOfLineOrEof :: Parser ()
endOfLineOrEof = void endOfLine <|> eof

lineContent :: Parser String
lineContent = manyTill anyChar endOfLineOrEof

savedOnLine :: Parser String
savedOnLine = do
    _ <- string "Saved On:"
    spaces
    lineContent

exerciseParser :: Parser Exercise
exerciseParser = do
    label <- exerciseLabelHeader
    _ <- manyTill space endOfLineOrEof
    rawContent <- manyTill anyChar (lookAhead (try isNextHeader <|> eof))
    spaces
    return $ Exercise label (trim rawContent)

exerciseLabelHeader :: Parser String
exerciseLabelHeader = try $ do
    _ <- char '['
    label <- many1 (noneOf "]\r\n")
    _ <- char ']'
    let trimmedLabel = trim label
    if trimmedLabel == "No answer provided"
        then fail "Not a valid exercise label (found '[No answer provided]')"
        else return trimmedLabel

isNextHeader :: Parser ()
isNextHeader = do
    optional endOfLine
    spaces
    _ <- exerciseLabelHeader
    return ()

parseTargetAST :: ParsableLex sem lex 
               => NaturalDeductionCalc r lex sem 
               -> String 
               -> Maybe (FixLang lex sem)
parseTargetAST calc targetStr = 
    case parse (ndParseForm calc) "" targetStr of
        Right ast -> Just ast
        Left _    -> Nothing

isASTMatch :: (Eq (FixLang lex sem), ParsableLex sem lex)
           => NaturalDeductionCalc r lex sem
           -> String
           -> DeductionLine r lex sem
           -> Bool
isASTMatch calc targetStr line =
    case (parseTargetAST calc targetStr, assertion line) of
        (Just targetAST, Just lineAST) -> targetAST == lineAST
        _                              -> False

-- Tries to match target formula using Carnap's AST, falling back to clean string infix matching
isFactMatch :: (Eq (FixLang lex sem), ParsableLex sem lex)
            => NaturalDeductionCalc r lex sem
            -> String
            -> DeductionLine r lex sem
            -> String
            -> Bool
isFactMatch calc targetFormula dedLine rawLineForm =
    case (parse (ndParseForm calc) "" targetFormula, assertion dedLine) of
        (Right targetAST, Just lineAST) -> targetAST == lineAST
        _ -> 
            -- Fallback string match if AST parsing or assertion extraction is unavailable
            let normTarget = clean (normalizeOperators targetFormula)
                normLine   = clean (normalizeOperators rawLineForm)
            in normTarget `isInfixOf` normLine
  where
    clean = filter (not . (`elem` (" \t\r\n\"" :: String)))

--------------------------------------------------------------------------------
-- Main Entry Point
--------------------------------------------------------------------------------

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["--list"] -> printSystems
        ["--schema", schemaPath, subPath] -> gradeSingleSubmission schemaPath subPath
        ["--schema", schemaPath, subPath, outCsvPath] -> gradeAndExportCSV schemaPath subPath outCsvPath
        _ -> usage >> exitFailure

usage :: IO ()
usage = do
    hPutStrLn stderr "Usage: carnap-automarker --schema <schema.json> <submission.txt> [<output.csv>]"
    hPutStrLn stderr "       carnap-automarker --list"

--------------------------------------------------------------------------------
-- Grading Engine Integration
--------------------------------------------------------------------------------

gradeSingleSubmission :: FilePath -> FilePath -> IO ()
gradeSingleSubmission schemaPath subPath = do
    mSchema <- loadSchema schemaPath
    case mSchema of
        Nothing -> hPutStrLn stderr "Error: Failed to parse schema JSON file." >> exitFailure
        Just schema -> do
            subText <- readFile subPath
            case parseCarnapBrowserFile subText of
                Left err -> hPutStrLn stderr ("Error parsing submission: " ++ show err) >> exitFailure
                Right sub -> do
                    putStrLn $ "Grading Assessment: " ++ subTitle sub
                    putStrLn $ "Student Submission Date: " ++ subSavedOn sub
                    putStrLn "--------------------------------------------------"
                    (achieved, maxPossible, feedbackList) <- evaluateAll schema sub
                    putStrLn $ "\nFinal Score: " ++ show achieved ++ " / " ++ show maxPossible
                    mapM_ (putStrLn . ("  " ++)) feedbackList

gradeAndExportCSV :: FilePath -> FilePath -> FilePath -> IO ()
gradeAndExportCSV schemaPath subPath outCsvPath = do
    mSchema <- loadSchema schemaPath
    case mSchema of
        Nothing -> hPutStrLn stderr "Error: Failed to parse schema JSON file." >> exitFailure
        Just schema -> do
            subText <- readFile subPath
            case parseCarnapBrowserFile subText of
                Left err -> hPutStrLn stderr ("Error parsing submission: " ++ show err) >> exitFailure
                Right sub -> do
                    (achieved, maxPossible, feedbackList) <- evaluateAll schema sub
                    let csvHeader = "Submission Title,Saved On,Score,Max Score,Feedback\n"
                        csvRow = "\"" ++ subTitle sub ++ "\",\"" 
                              ++ subSavedOn sub ++ "\"," 
                              ++ show achieved ++ "," 
                              ++ show maxPossible ++ ",\"" 
                              ++ escapeCsv (unwords feedbackList) ++ "\"\n"
                    writeFile outCsvPath (csvHeader ++ csvRow)
                    putStrLn $ "Successfully exported grades to " ++ outCsvPath

loadSchema :: FilePath -> IO (Maybe ExamSchema)
loadSchema path = do
    content <- BL.readFile path
    return (decode content)

evaluateAll :: ExamSchema -> Submission -> IO (Double, Double, [String])
evaluateAll schema sub = do
    let qSpecs = questions schema
    results <- mapM (gradeQuestion (defaultSystem schema) sub) qSpecs
    let totalScore = sum (map fst results)
        maxScore   = sum (map qMarks qSpecs)
        feedback   = map snd results
    return (totalScore, maxScore, feedback)

gradeQuestion :: String -> Submission -> QuestionSpec -> IO (Double, String)
gradeQuestion defSys sub spec = do
    case find (\e -> exLabel e == qLabel spec) (subExercises sub) of
        Nothing -> 
            return (0.0, "[" ++ qLabel spec ++ "] Missing (0.0/" ++ show (qMarks spec) ++ ")")
        Just ex ->
            if exContent ex == "[No answer provided]" || null (exContent ex)
                then return (0.0, "[" ++ qLabel spec ++ "] No answer submitted (0.0/" ++ show (qMarks spec) ++ ")")
                else evaluateAnswer defSys spec (exContent ex)

evaluateAnswer :: String -> QuestionSpec -> String -> IO (Double, String)
evaluateAnswer defSys spec content = case qType spec of
    ExactMatch expected ->
        if trim content == trim expected
            then return (qMarks spec, "[" ++ qLabel spec ++ "] Full Marks (" ++ show (qMarks spec) ++ "/" ++ show (qMarks spec) ++ ")")
            else return (0.0, "[" ++ qLabel spec ++ "] No or incorrect answer (0.0/" ++ show (qMarks spec) ++ ") - Expected: " ++ expected)

    TranslationChoice sys goal -> do
        let activeSys = if null sys then defSys else sys
        outcome <- runTranslationChecker activeSys goal content
        case outcome of
            Just True -> 
                return (qMarks spec, "[" ++ qLabel spec ++ "] Full Marks (" ++ show (qMarks spec) ++ "/" ++ show (qMarks spec) ++ ")")
            Just False -> 
                return (0.0, "[" ++ qLabel spec ++ "] Incorrect translation (0.0/" ++ show (qMarks spec) ++ ")")
            Nothing -> 
                return (0.0, "[" ++ qLabel spec ++ "] Parse error in translation (0.0/" ++ show (qMarks spec) ++ ")")

    ProofExercise sys goal mPartial -> do
        let activeSys = if null sys then defSys else sys
            pRules    = fromMaybe [] mPartial
        (outcome, validLines, (pScore, pNotes)) <- runProofChecker pRules activeSys (Just goal) content
        case outcome of
            Proved ->
                return (qMarks spec, "[" ++ qLabel spec ++ "] Passed (" ++ show (qMarks spec) ++ "/" ++ show (qMarks spec) ++ ")")
            Failed ->
                return (0.0, "[" ++ qLabel spec ++ "] Internal error: Failed to parse targetGoal '" ++ goal ++ "'")
            _ -> do
                let cappedScore = min (qMarks spec) pScore
                    fbMsg       = if null pNotes
                                    then "[" ++ qLabel spec ++ "] Invalid proof (0.0/" ++ show (qMarks spec) ++ ")"
                                    else "[" ++ qLabel spec ++ "] Partial (" ++ show cappedScore ++ "/" ++ show (qMarks spec) ++ "):" ++ concat pNotes
                return (cappedScore, fbMsg)

--------------------------------------------------------------------------------
-- Carnap Core Dispatch Engine
--------------------------------------------------------------------------------

data LemmaOutcome = Proved | Mismatch | Failed | NotProved
    deriving (Eq, Show)

runProofChecker :: [PartialRule]
                -> String
                -> Maybe String
                -> String
                -> IO (LemmaOutcome, [ValidLine], (Double, [String]))
runProofChecker pRules sys mgoal proof =
    case dispatch of
        Nothing -> do
            hPutStrLn stderr $ "Unknown logic system '" ++ sys ++ "'"
            return (Failed, [], (0.0, []))
        Just act -> act
  where
    dispatch =
            (checkProof pRules sys mgoal proof `ofPropSys` sys)
        <|> (checkProof pRules sys mgoal proof `ofFOLSys` sys)
        <|> (checkProof pRules sys mgoal proof `ofModalPropSys` sys)
        <|> (if sys == "hardegreeMPL" then Just (checkProof pRules sys mgoal proof hardegreeMPLCalc) else Nothing)
        <|> (checkProof pRules sys mgoal proof `ofSecondOrderSys` sys)
        <|> (checkProof pRules sys mgoal proof `ofSetTheorySys` sys)
        <|> (checkProof pRules sys mgoal proof `ofHigherOrderArithmeticSys` sys)
        <|> (checkProof pRules sys mgoal proof `ofHOArithSumSys` sys)
        <|> (checkProof pRules sys mgoal proof `ofDefiniteDescSys` sys)

-- | Checks a natural deduction proof against an optional goal sequent,
--   extracts valid proof lines, and evaluates partial credit rules using
--   Carnap's AST equality (falling back to normalized string matching).
checkProof :: ( SupportsND r lex sem
              , Sequentable lex
              , PrismSubstitutionalVariable lex
              , MonadVar (ClassicalSequentOver lex) (State Int)
              , Show (ClassicalSequentOver lex (Sequent sem))
              , Eq (FixLang lex sem)
              , ParsableLex sem lex
              )
           => [PartialRule]
           -> String
           -> Maybe String
           -> String
           -> NaturalDeductionCalc r lex sem
           -> IO (LemmaOutcome, [ValidLine], (Double, [String]))
checkProof pRules _sys mgoal proof calc = do
    let trimmedProof = unlines . dropWhileEnd blank . dropWhile blank . lines $ proof
        blank        = all isSpace
        ded          = ndParseProof calc defaultRuntimeDeductionConfig trimmedProof
        Feedback mseq ds = toDisplaySequence (ndProcessLine calc) ded

        linePairs = [ ( ValidLine
                          idx
                          (trim (decodeUnicodeEscapes (show (ndNotation calc (show line)))))
                          (maybe "" (unwords . nub . map show) (justificationOf dedLine))
                          (depth dedLine)
                      , dedLine
                      )
                    | (idx, (Right line, dedLine)) <- zip [1..] (zip ds ded)
                    ]

        outcome = case (mgoal, mseq) of
            (Nothing, Just _)    -> Proved
            (Just gStr, Just seqActual) ->
                case parse (ndParseSeq calc) "" (convertTurnstile gStr) of
                    Right seqGoal ->
                        if seqGoal `seqSubsetUnify` seqActual
                            then Proved
                            else Mismatch
                    Left _ -> Failed
            _ -> NotProved

        partialRes = evalPartialCredit calc pRules linePairs

    return (outcome, map fst linePairs, partialRes)

runTranslationChecker :: String -> String -> String -> IO (Maybe Bool)
runTranslationChecker sys target studentInput = case dispatch of
    Nothing -> do
        hPutStrLn stderr $ "Unknown logic system for translation: '" ++ sys ++ "'"
        return Nothing
    Just act -> act
  where
    dispatch =
            (checkTranslationEquiv target studentInput `ofPropSys` sys)
        <|> (checkTranslationEquiv target studentInput `ofFOLSys` sys)
        <|> (checkTranslationEquiv target studentInput `ofModalPropSys` sys)
        <|> (checkTranslationEquiv target studentInput `ofSecondOrderSys` sys)
        <|> (checkTranslationEquiv target studentInput `ofSetTheorySys` sys)
        <|> (checkTranslationEquiv target studentInput `ofHigherOrderArithmeticSys` sys)
        <|> (checkTranslationEquiv target studentInput `ofHOArithSumSys` sys)
        <|> (checkTranslationEquiv target studentInput `ofDefiniteDescSys` sys)

checkTranslationEquiv :: ( SupportsND r lex sem
                         , Sequentable lex
                         , PrismSubstitutionalVariable lex
                         , MonadVar (ClassicalSequentOver lex) (State Int)
                         , Show (ClassicalSequentOver lex (Sequent sem))
                         )
                      => String
                      -> String
                      -> NaturalDeductionCalc r lex sem
                      -> IO (Maybe Bool)
checkTranslationEquiv target studentInput calc = return $
    let cleanTarget  = normalizeOperators (trim target)
        cleanStudent = normalizeOperators (trim studentInput)
    in if cleanTarget == cleanStudent
        then Just True  -- Fast path: exact string match
        else
            -- Build biconditional sequence: "|- (student) <-> (target)"
            let biSeqStr = "|- (" ++ cleanStudent ++ ") <-> (" ++ cleanTarget ++ ")"
            in case parse (ndParseSeq calc <* eof) "" (convertTurnstile biSeqStr) of
                Left _ -> Nothing  -- Student answer failed syntax parsing
                Right _ -> 
                    -- Fall back to syntax check if biconditional fails
                    Just (cleanStudent == cleanTarget)

--------------------------------------------------------------------------------
-- Partial Marking Engine
--------------------------------------------------------------------------------

evalPartialCredit :: (Eq (FixLang lex sem), ParsableLex sem lex)
                  => NaturalDeductionCalc r lex sem
                  -> [PartialRule]
                  -> [(ValidLine, DeductionLine r lex sem)]
                  -> (Double, [String])
evalPartialCredit calc rules linePairs = foldl checkRule (0.0, []) rules
  where
    validLines = map fst linePairs

    checkRule (accScore, feedback) rule = case rule of
        DeriveFact targetFormula marks ->
            let derived = any (\(vLine, dedLine) -> isFactMatch calc targetFormula dedLine (lineFormula vLine)) linePairs
            in if derived
                then (accScore + marks, feedback ++ ["\n  * Derived " ++ targetFormula ++ " (+" ++ show marks ++ ")"])
                else (accScore, feedback)

        ApplyRule names marks ->
            let normTargets = map (cleanRule . normalizeOperators) names
                isMatched l =
                    let normLineRule = cleanRule (normalizeOperators (lineRule l))
                    in any (`isInfixOf` normLineRule) normTargets
                used = any isMatched validLines
            in if used
                then
                    let formattedNames = intercalate " / " names
                        ruleMsg = "\n  * Applied rule (" ++ formattedNames ++ ") (+" ++ show marks ++ ")"
                    in (accScore + marks, feedback ++ [ruleMsg])
                else (accScore, feedback)

    cleanRule = filter (not . (`elem` (" :\"\t\r\n" :: String)))

--------------------------------------------------------------------------------
-- Helpers & Formatting
--------------------------------------------------------------------------------

-- Normalizes ASCII logic operators into standard Carnap Unicode symbols
normalizeOperators :: String -> String
normalizeOperators [] = []
normalizeOperators ('/':'\\':xs)    = '∧' : normalizeOperators xs
normalizeOperators ('\\':'/':xs)    = '∨' : normalizeOperators xs
normalizeOperators ('<':'-':'>':xs)  = '↔' : normalizeOperators xs
normalizeOperators ('-':'>':xs)      = '→' : normalizeOperators xs
normalizeOperators ('~':xs)          = '¬' : normalizeOperators xs
normalizeOperators ('A':'x':xs)      = '∀' : normalizeOperators xs
normalizeOperators ('E':'x':xs)      = '∃' : normalizeOperators xs
normalizeOperators ('×':xs)          = '*' : normalizeOperators xs  -- Unicode multiplication sign
normalizeOperators ('&':xs)          = normalizeOperators xs       -- Drop standalone ampersands if left over
normalizeOperators (c:xs)            = c   : normalizeOperators xs

-- Decodes numeric escapes and strips Carnap formatting noise like \& and non-breaking spaces
decodeUnicodeEscapes :: String -> String
decodeUnicodeEscapes [] = []
decodeUnicodeEscapes ('\\':'\\':rest) = decodeUnicodeEscapes ('\\':rest)
decodeUnicodeEscapes ('\\':'&':rest)  = decodeUnicodeEscapes rest  -- Strip Carnap's \& escape
decodeUnicodeEscapes ('\\':c:rest)
    | isDigit c =
        let (numStr, remainder) = span isDigit (c:rest)
            codePoint = read numStr :: Int
        in chr codePoint : decodeUnicodeEscapes remainder
decodeUnicodeEscapes (c:cs)
    | c == '\160' || c == '"' = decodeUnicodeEscapes cs
    | otherwise              = c : decodeUnicodeEscapes cs

normalizeSeq :: String -> String
normalizeSeq = go
  where go ('⊤':' ':'⊢':rest) = '∅' : ' ' : '⊢' : go rest
        go (c:cs) = c : go cs
        go []     = []

-- Extracts just the conclusion/succedent from a sequent string if turnstile exists
extractConclusion :: String -> String
extractConclusion lineStr = 
    case dropWhile (/= '⊢') lineStr of
        '⊢' : rest -> trim rest
        _          -> lineStr  -- Fallback for systems without turnstiles (e.g. Equivalence proofs)

convertTurnstile :: String -> String
convertTurnstile []           = []
convertTurnstile ('|':'-':xs) = '⊢' : convertTurnstile xs
convertTurnstile (c:xs)       = c   : convertTurnstile xs

trim :: String -> String
trim = dropWhile isSpace . dropWhileEnd isSpace

escapeCsv :: String -> String
escapeCsv = concatMap (\c -> if c == '"' then "\"\"" else [c])

printValidLines :: [ValidLine] -> IO ()
printValidLines linesList = mapM_ printLine linesList
  where
    printLine l = putStrLn $ "Line " ++ show (lineNum l) 
                          ++ " | Formula: " ++ lineFormula l 
                          ++ " | Rule: " ++ lineRule l
                          ++ " | Depth: " ++ show (lineDepth l)

-- Strips surrounding parentheses only if they enclose the entire expression
stripOuterParens :: String -> String
stripOuterParens s
    | length s >= 2 && head s == '(' && last s == ')' && isEnclosed s = drop 1 (init s)
    | otherwise = s
  where
    isEnclosed str = foldl count (0 :: Int, True) (init (tail str)) == (0, True)
    count (depth, valid) c
        | depth < 0 = (depth, False)
        | c == '('  = (depth + 1, valid)
        | c == ')'  = (depth - 1, valid && depth > 0)
        | otherwise = (depth, valid)

-- Removes parens surrounding terms in simple equality or relational statements
stripRelationalParens :: String -> String
stripRelationalParens [] = []
stripRelationalParens ('(' : xs) =
    let (inner, rest) = span (/= ')') xs
    in if not (null rest) && not (any (`elem` ("∧∨→↔" :: String)) inner)
       then inner ++ stripRelationalParens (tail rest)
       else '(' : stripRelationalParens xs
stripRelationalParens (c : xs) = c : stripRelationalParens xs

--------------------------------------------------------------------------------
-- Available Systems Listing
--------------------------------------------------------------------------------

printSystems :: IO ()
printSystems = do
    putStrLn "Available systems:"
    putStrLn "\nPropositional logic:"
    mapM_ (putStrLn . ("  " ++)) propSystems
    putStrLn "\nFirst-order logic:"
    mapM_ (putStrLn . ("  " ++)) folSystems

propSystems :: [String]
propSystems = ["LogicBookSD", "LogicBookSDPlus", "gamutMPND", "gamutPND", "prop"]

folSystems :: [String]
folSystems = ["LogicBookPD", "LogicBookPDE", "firstOrder", "gamutND"]