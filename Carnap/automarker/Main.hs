{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}

module Main where

import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath ((</>), takeExtension, takeBaseName)
import System.IO (hPutStrLn, stderr, readFile, writeFile)
import Control.Applicative ((<|>))
import Control.Monad (void, foldM, when)
import Data.Char (isSpace, isDigit, chr, toLower)
import Data.List (dropWhileEnd, isInfixOf, find, nub, intercalate, sort)
import Data.Maybe (fromMaybe, isJust)
import Data.Aeson (FromJSON, ToJSON, decode)
import qualified Data.ByteString.Lazy as BL
import GHC.Generics (Generic)
import Text.Parsec hiding ((<|>), State)
import Text.Parsec.String (Parser)
import Text.Parsec.Error (errorMessages, errorPos, showErrorMessages)
import Text.Parsec.Pos (sourceColumn)
import Text.Printf (printf)
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
    = DeriveFact { factFormula :: String, factRule :: Maybe [String], factMarks :: Double }
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
        , targetGoals :: [String]
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

data SubmissionResult = SubmissionResult
    { resFile           :: FilePath
    , resStudentId      :: String
    , resTitle          :: String
    , resSavedOn        :: String
    , resTotal          :: Double
    , resMax            :: Double
    , resQuestionScores :: [(String, Double)]  -- (qLabel, awardedMarks)
    , resFeedback       :: [String]
    } deriving (Show)

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

-- | Matches a target formula against a proof line up to alpha-renaming
--   using Carnap's sequent unification (seqSubsetUnify), falling back
--   to AST equality and normalized string matching.
isFactMatch :: ( SupportsND r lex sem
               , Sequentable lex
               , PrismSubstitutionalVariable lex
               , MonadVar (ClassicalSequentOver lex) (State Int)
               , Show (ClassicalSequentOver lex (Sequent sem))
               , Eq (FixLang lex sem)
               , ParsableLex sem lex
               )
            => NaturalDeductionCalc r lex sem
            -> String
            -> DeductionLine r lex sem
            -> String
            -> Bool
isFactMatch calc targetFormula dedLine rawLineForm =
    let targetSeqStr = "⊢ " ++ normalizeOperators (convertTurnstile (trim targetFormula))
        lineFormOnly = extractConclusion rawLineForm
        lineSeqStr   = "⊢ " ++ normalizeOperators (convertTurnstile (trim lineFormOnly))
    in case (parse (ndParseSeq calc) "" targetSeqStr, parse (ndParseSeq calc) "" lineSeqStr) of
        (Right targetSeq, Right lineSeq) ->
            (targetSeq `seqSubsetUnify` lineSeq) && (lineSeq `seqSubsetUnify` targetSeq)
        _ ->
            case (parse (ndParseForm calc) "" (normalizeOperators targetFormula), assertion dedLine) of
                (Right targetAST, Just lineAST) -> targetAST == lineAST
                _ ->
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
        ("--schema" : schemaPath : rest) -> parseRunArgs schemaPath rest
        _ -> usage >> exitFailure

parseRunArgs :: FilePath -> [String] -> IO ()
parseRunArgs schemaPath rest = case extractCsvFlag rest of
    (Just outCsv, inputs@(_:_)) -> runBatch schemaPath inputs (Just outCsv)
    (Nothing, [subPath, outCsv]) | takeExtension outCsv == ".csv" ->
        runBatch schemaPath [subPath] (Just outCsv)
    (Nothing, inputs@(_:_)) -> runBatch schemaPath inputs Nothing
    _ -> usage >> exitFailure
  where
    extractCsvFlag ("--csv" : csvPath : xs) = (Just csvPath, xs)
    extractCsvFlag (x : xs) =
        let (mCsv, ys) = extractCsvFlag xs
        in (mCsv, x : ys)
    extractCsvFlag [] = (Nothing, [])

runBatch :: FilePath -> [FilePath] -> Maybe FilePath -> IO ()
runBatch schemaPath rawInputs mOutCsv = do
    mSchema <- loadSchema schemaPath
    case mSchema of
        Nothing -> hPutStrLn stderr "Error: Failed to parse schema JSON file." >> exitFailure
        Just schema -> do
            files <- resolveSubmissionPaths rawInputs
            if null files
                then hPutStrLn stderr "Error: No .txt submission files found." >> exitFailure
                else do
                    mResults <- mapM (gradeFile schema) files
                    let results = [ r | Just r <- mResults ]
                    mapM_ printStudentSummary results
                    when (length results > 1) $ printCohortReport schema results
                    case mOutCsv of
                        Just csvPath -> exportBatchCSV csvPath schema results
                        Nothing      -> return ()

printStudentSummary :: SubmissionResult -> IO ()
printStudentSummary r = do
    putStrLn $ "Student: " ++ resStudentId r ++ " (" ++ resTitle r ++ ")"
    putStrLn $ "Saved On: " ++ resSavedOn r
    putStrLn "--------------------------------------------------"
    mapM_ (putStrLn . ("  " ++)) (resFeedback r)
    printf "Final Score: %.2f / %.2f\n\n" (resTotal r) (resMax r)

usage :: IO ()
usage = do
    hPutStrLn stderr "Usage: carnap-automarker --schema <schema.json> [--csv <output.csv>] <file_or_dir> [<file_or_dir> ...]"
    hPutStrLn stderr "       carnap-automarker --list"

--------------------------------------------------------------------------------
-- Grading Engine Integration
--------------------------------------------------------------------------------

loadSchema :: FilePath -> IO (Maybe ExamSchema)
loadSchema path = do
    content <- BL.readFile path
    return (decode content)

evaluateAll :: ExamSchema -> FilePath -> Submission -> IO SubmissionResult
evaluateAll schema path sub = do
    let qSpecs = questions schema
    results <- mapM (gradeQuestion (defaultSystem schema) sub) qSpecs
    let qScores    = zip (map qLabel qSpecs) (map fst results)
        totalScore = sum (map fst results)
        maxScore   = sum (map qMarks qSpecs)
        feedback   = map snd results
    return SubmissionResult
        { resFile           = path
        , resStudentId      = takeBaseName path
        , resTitle          = subTitle sub
        , resSavedOn        = subSavedOn sub
        , resTotal          = totalScore
        , resMax            = maxScore
        , resQuestionScores = qScores
        , resFeedback       = feedback
        }

resolveSubmissionPaths :: [FilePath] -> IO [FilePath]
resolveSubmissionPaths paths = fmap (sort . concat) (mapM expandPath paths)
  where
    expandPath p = do
        isDir <- doesDirectoryExist p
        if isDir
            then do
                entries <- listDirectory p
                let txtFiles = filter (\f -> takeExtension f == ".txt") entries
                return (map (p </>) txtFiles)
            else return [p]

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
            then return (qMarks spec, "[" ++ qLabel spec ++ "] Full Marks Awarded (" ++ show (qMarks spec) ++ "/" ++ show (qMarks spec) ++ ")")
            else return (0.0, "[" ++ qLabel spec ++ "] No or incorrect answer (0.0/" ++ show (qMarks spec) ++ ") - Expected: " ++ expected)

    TranslationChoice sys goals -> do
        let activeSys = if null sys then defSys else sys
        outcome <- runTranslationChecker activeSys goals content
        case outcome of
            Just True -> 
                return (qMarks spec, "[" ++ qLabel spec ++ "] Formula Correct: Full Marks Awarded (" ++ show (qMarks spec) ++ "/" ++ show (qMarks spec) ++ ")")
            Just False -> 
                return (0.0, "[" ++ qLabel spec ++ "] Incorrect formula (0.0/" ++ show (qMarks spec) ++ ")")
            Nothing -> 
                return (0.0, "[" ++ qLabel spec ++ "] Parse error in formula (0.0/" ++ show (qMarks spec) ++ ")")

    ProofExercise sys goal mPartial -> do
        let activeSys = if null sys then defSys else sys
            pRules    = fromMaybe [] mPartial
        (outcome, validLines, (pScore, pNotes)) <- runProofChecker pRules activeSys (Just goal) content
        case outcome of
            Proved ->
                return (qMarks spec, "[" ++ qLabel spec ++ "] Complete Proof: Full Marks Awarded (" ++ show (qMarks spec) ++ "/" ++ show (qMarks spec) ++ ")")
            Failed ->
                return (0.0, "[" ++ qLabel spec ++ "] Internal error: Failed to parse targetGoal '" ++ goal ++ "'")
            _ -> do
                let cappedScore = min (qMarks spec) pScore
                    fbMsg       = if null pNotes
                                    then "[" ++ qLabel spec ++ "] No or incorrect proof provided (0.0/" ++ show (qMarks spec) ++ ")"
                                    else "[" ++ qLabel spec ++ "] Incomplete Proof: Partial Marks Awarded (" ++ show cappedScore ++ "/" ++ show (qMarks spec) ++ "):" ++ concat pNotes
                return (cappedScore, fbMsg)

gradeFile :: ExamSchema -> FilePath -> IO (Maybe SubmissionResult)
gradeFile schema path = do
    subText <- readFile path
    case parseCarnapBrowserFile subText of
        Left err -> do
            hPutStrLn stderr $ "Warning: Skipping '" ++ path ++ "' (parse error: " ++ show err ++ ")"
            return Nothing
        Right sub -> Just <$> evaluateAll schema path sub

--------------------------------------------------------------------------------
-- Cohort Statistics
--------------------------------------------------------------------------------

data CohortStats = CohortStats
    { statCount  :: Int
    , statMaxPos :: Double
    , statMean   :: Double
    , statMedian :: Double
    , statStdDev :: Double
    , statMin    :: Double
    , statMax    :: Double
    , statQ1     :: Double
    , statQ3     :: Double
    } deriving (Show)

computeStats :: [SubmissionResult] -> CohortStats
computeStats [] = CohortStats 0 0 0 0 0 0 0 0 0
computeStats results =
    let scores = sort (map resTotal results)
        n      = length scores
        nD     = fromIntegral n
        maxPos = maybe 0 resMax (listToMaybe results)
        mean   = sum scores / nD
        med    = percentile scores 0.50
        q1     = percentile scores 0.25
        q3     = percentile scores 0.75
        -- Sample standard deviation (Bessel-corrected when n > 1)
        var    = if n > 1
                   then sum (map (\x -> (x - mean) ^ (2 :: Int)) scores) / (nD - 1)
                   else 0.0
    in CohortStats
        { statCount  = n
        , statMaxPos = maxPos
        , statMean   = mean
        , statMedian = med
        , statStdDev = sqrt var
        , statMin    = head scores
        , statMax    = last scores
        , statQ1     = q1
        , statQ3     = q3
        }
  where
    listToMaybe []    = Nothing
    listToMaybe (x:_) = Just x

-- Linear-interpolation percentile on a sorted non-empty list
percentile :: [Double] -> Double -> Double
percentile xs p =
    let n   = length xs
        idx = p * fromIntegral (n - 1)
        lo  = floor idx
        hi  = ceiling idx
        w   = idx - fromIntegral lo
    in if lo == hi
         then xs !! lo
         else (xs !! lo) * (1 - w) + (xs !! hi) * w

printCohortReport :: ExamSchema -> [SubmissionResult] -> IO ()
printCohortReport _ [] = putStrLn "No valid submissions graded."
printCohortReport schema results = do
    let s = computeStats results
        pct x = if statMaxPos s > 0 then (x / statMaxPos s) * 100 else 0
    putStrLn "\n=================================================="
    putStrLn $ "COHORT SUMMARY (" ++ examTitle schema ++ ")"
    putStrLn "=================================================="
    printf "Submissions Graded : %d\n" (statCount s)
    printf "Mean Score         : %.2f / %.2f (%.1f%%)\n" (statMean s) (statMaxPos s) (pct (statMean s))
    printf "Median Score       : %.2f (IQR: %.2f - %.2f)\n" (statMedian s) (statQ1 s) (statQ3 s)
    printf "Std Deviation      : %.2f\n" (statStdDev s)
    printf "Min / Max          : %.2f / %.2f\n" (statMin s) (statMax s)

    putStrLn "\nPer-Question Breakdown:"
    mapM_ (printQuestionStat results) (questions schema)

printQuestionStat :: [SubmissionResult] -> QuestionSpec -> IO ()
printQuestionStat results spec = do
    let lbl     = qLabel spec
        maxM    = qMarks spec
        qScores = [ sc | r <- results, (l, sc) <- resQuestionScores r, l == lbl ]
        n       = length qScores
        avg     = if n > 0 then sum qScores / fromIntegral n else 0
        fullCnt = length (filter (>= maxM - 1e-6) qScores)
        pct     = if maxM > 0 then (avg / maxM) * 100 else 0
    printf "  [%-4s] Avg: %5.2f / %5.2f (%5.1f%%) | Full Marks: %d/%d\n"
           lbl avg maxM pct fullCnt n

exportBatchCSV :: FilePath -> ExamSchema -> [SubmissionResult] -> IO ()
exportBatchCSV outCsvPath schema results = do
    let qLabels = map qLabel (questions schema)
        header  = intercalate ","
                    ( ["Student ID", "File", "Submission Title", "Saved On", "Total Score", "Max Score", "Percentage"]
                      ++ qLabels
                      ++ ["Feedback"]
                    ) ++ "\n"
        rows    = concatMap (toCsvRow qLabels) results
        bom     = "\xFEFF"
    writeFile outCsvPath (bom ++ header ++ rows)
    putStrLn $ "\nExported " ++ show (length results) ++ " graded submissions to " ++ outCsvPath
  where
    toCsvRow qLabels r =
        let pct = if resMax r > 0 then (resTotal r / resMax r) * 100 else 0
            qCols = [ printf "%.2f" (fromMaybe 0.0 (lookup lbl (resQuestionScores r))) | lbl <- qLabels ]
            baseCols =
                [ quote (resStudentId r)
                , quote (resFile r)
                , quote (resTitle r)
                , quote (resSavedOn r)
                , printf "%.2f" (resTotal r)
                , printf "%.2f" (resMax r)
                , printf "%.1f" pct
                ]
            htmlFeedback = intercalate "<br>" (map newlinesToBr (resFeedback r))
            fbCol = [ quote htmlFeedback ]
        in intercalate "," (baseCols ++ qCols ++ fbCol) ++ "\n"

    newlinesToBr :: String -> String
    newlinesToBr []            = []
    newlinesToBr ('\r':'\n':xs) = "<br>" ++ newlinesToBr xs
    newlinesToBr ('\n':xs)      = "<br>" ++ newlinesToBr xs
    newlinesToBr (x:xs)         = x : newlinesToBr xs

    quote s = "\"" ++ escapeCsv s ++ "\""

    escapeCsv []       = []
    escapeCsv ('"':xs) = '"' : '"' : escapeCsv xs
    escapeCsv (x:xs)   = x : escapeCsv xs

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

runTranslationChecker :: String -> [String] -> String -> IO (Maybe Bool)
runTranslationChecker sys targets studentInput = case dispatch of
    Nothing -> do
        hPutStrLn stderr $ "Unknown logic system for translation: '" ++ sys ++ "'"
        return Nothing
    Just act -> act
  where
    dispatch =
            (checkTranslationEquiv targets studentInput `ofPropSys` sys)
        <|> (checkTranslationEquiv targets studentInput `ofFOLSys` sys)
        <|> (checkTranslationEquiv targets studentInput `ofModalPropSys` sys)
        <|> (checkTranslationEquiv targets studentInput `ofSecondOrderSys` sys)
        <|> (checkTranslationEquiv targets studentInput `ofSetTheorySys` sys)
        <|> (checkTranslationEquiv targets studentInput `ofHigherOrderArithmeticSys` sys)
        <|> (checkTranslationEquiv targets studentInput `ofHOArithSumSys` sys)
        <|> (checkTranslationEquiv targets studentInput `ofDefiniteDescSys` sys)

checkTranslationEquiv :: ( SupportsND r lex sem
                         , Sequentable lex
                         , PrismSubstitutionalVariable lex
                         , MonadVar (ClassicalSequentOver lex) (State Int)
                         , Show (ClassicalSequentOver lex (Sequent sem))
                         , Eq (FixLang lex sem)
                         , ParsableLex sem lex
                         )
                      => [String]
                      -> String
                      -> NaturalDeductionCalc r lex sem
                      -> IO (Maybe Bool)
checkTranslationEquiv targets studentInput calc = return $
    let cleanStudent = normalizeOperators (trim studentInput)
    in case parse (ndParseSeq calc <* eof) "" ("⊢ " ++ cleanStudent) of
        Left _ -> Nothing  -- Student answer failed syntax parsing
        Right studentSeq ->
            let matchesTarget rawTarget =
                    let cleanTarget = normalizeOperators (trim rawTarget)
                    in cleanTarget == cleanStudent
                       || case parse (ndParseSeq calc <* eof) "" ("⊢ " ++ cleanTarget) of
                            Right targetSeq ->
                                ((targetSeq `seqSubsetUnify` studentSeq) && (studentSeq `seqSubsetUnify` targetSeq))
                            Left _ -> False
            in Just (any matchesTarget targets)

--------------------------------------------------------------------------------
-- Partial Marking Engine
--------------------------------------------------------------------------------
evalPartialCredit :: ( SupportsND r lex sem
                     , Sequentable lex
                     , PrismSubstitutionalVariable lex
                     , MonadVar (ClassicalSequentOver lex) (State Int)
                     , Show (ClassicalSequentOver lex (Sequent sem))
                     , Eq (FixLang lex sem)
                     , ParsableLex sem lex
                     )
                  => NaturalDeductionCalc r lex sem
                  -> [PartialRule]
                  -> [(ValidLine, DeductionLine r lex sem)]
                  -> (Double, [String])
evalPartialCredit calc rules linePairs = foldl checkRule (0.0, []) rules
  where
    validLines = map fst linePairs

    matchesRule :: [String] -> ValidLine -> Bool
    matchesRule targetNames vLine =
        let normTargets  = map (cleanRule . normalizeOperators) targetNames
            normLineRule = cleanRule (normalizeOperators (lineRule vLine))
        in normLineRule `elem` normTargets

    checkRule (accScore, feedback) rule = case rule of
        DeriveFact targetFormula mRuleNames marks ->
            let isLineMatch (vLine, dedLine) =
                    isFactMatch calc targetFormula dedLine (lineFormula vLine)
                    && maybe True (`matchesRule` vLine) mRuleNames
                derived = any isLineMatch linePairs
            in if derived
                then
                    let ruleSuffix = case mRuleNames of
                            Just rs | not (null rs) -> " using " ++ intercalate " / " rs
                            _                       -> ""
                        msg = "\n  * Derived " ++ targetFormula ++ ruleSuffix ++ " (+" ++ show marks ++ ")"
                    in (accScore + marks, feedback ++ [msg])
                else (accScore, feedback)

        ApplyRule names marks ->
            let used = any (matchesRule names) validLines
            in if used
                then
                    let formattedNames = intercalate " / " names
                        ruleMsg = "\n  * Applied rule (" ++ formattedNames ++ ") (+" ++ show marks ++ ")"
                    in (accScore + marks, feedback ++ [ruleMsg])
                else (accScore, feedback)

    cleanRule = map toLower . filter (not . (`elem` (" :\"\t\r\n" :: String)))

--------------------------------------------------------------------------------
-- Helpers & Formatting
--------------------------------------------------------------------------------

-- Normalizes ASCII logic operators into standard Carnap Unicode symbols
normalizeOperators :: String -> String
normalizeOperators [] = []
normalizeOperators ('|':'-':xs)     = '⊢' : normalizeOperators xs
normalizeOperators ('|':xs)         = '∨' : normalizeOperators xs
normalizeOperators ('/':'\\':xs)    = '∧' : normalizeOperators xs
normalizeOperators ('^':xs)         = '∧' : normalizeOperators xs
normalizeOperators ('\\':'/':xs)    = '∨' : normalizeOperators xs
normalizeOperators ('<':'-':'>':xs)  = '↔' : normalizeOperators xs
normalizeOperators ('-':'>':xs)      = '→' : normalizeOperators xs
normalizeOperators ('~':xs)          = '¬' : normalizeOperators xs
normalizeOperators ('A':xs)      = '∀' : normalizeOperators xs
normalizeOperators ('E':xs)      = '∃' : normalizeOperators xs
normalizeOperators ('×':xs)          = '*' : normalizeOperators xs
normalizeOperators ('&':xs)          = '∧' : normalizeOperators xs
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