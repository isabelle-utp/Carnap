{-#LANGUAGE RankNTypes, FlexibleContexts #-}

module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import Control.Applicative ((<|>))
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
import Carnap.Languages.DefiniteDescription.Logic.Gamut (ofDefiniteDescSys)
import Control.Monad.State (State)
import Data.Char (isSpace)
import Text.Parsec.Error (errorMessages, errorPos, showErrorMessages)
import Text.Parsec.Pos (sourceColumn)

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["--list"] -> printSystems
        [sys, filepath] -> do
            proofText <- readFile filepath
            let result = dispatchProp proofText sys
                     <|> dispatchFOL  proofText sys
                     <|> dispatchModalProp proofText sys
                     <|> dispatchModalFOL proofText sys
                     <|> dispatchSecondOrder proofText sys
                     <|> dispatchSetTheory proofText sys
                     <|> dispatchHOArith proofText sys
                     <|> dispatchDefiniteDesc proofText sys
            case result of
                Nothing -> do
                    hPutStrLn stderr $ "Unknown system: " ++ sys
                    hPutStrLn stderr "Use --list to see available systems."
                    exitFailure
                Just action -> action
        _ -> do
            hPutStrLn stderr "Usage: carnap-check <system> <file>"
            hPutStrLn stderr "       carnap-check --list"
            exitFailure

runCalc :: ( SupportsND r lex sem
           , Sequentable lex
           , PrismSubstitutionalVariable lex
           , MonadVar (ClassicalSequentOver lex) (State Int)
           , Show (ClassicalSequentOver lex (Sequent sem))
           ) => String -> NaturalDeductionCalc r lex sem -> IO ()
runCalc proofText ndcalc = do
    let pt  = strip proofText
        ded = ndParseProof ndcalc defaultRuntimeDeductionConfig pt
        Feedback mseq ds = toDisplaySequence (ndProcessLine ndcalc) ded
    presentResults (show <$> mseq) ds

dispatchProp :: String -> String -> Maybe (IO ())
dispatchProp proofText = ofPropSys (runCalc proofText)

dispatchFOL :: String -> String -> Maybe (IO ())
dispatchFOL proofText = ofFOLSys (runCalc proofText)

dispatchModalProp :: String -> String -> Maybe (IO ())
dispatchModalProp proofText = ofModalPropSys (runCalc proofText)

dispatchModalFOL :: String -> String -> Maybe (IO ())
dispatchModalFOL proofText sys
    | sys == "hardegreeMPL" = Just (runCalc proofText hardegreeMPLCalc)
    | otherwise             = Nothing

dispatchSecondOrder :: String -> String -> Maybe (IO ())
dispatchSecondOrder proofText = ofSecondOrderSys (runCalc proofText)

dispatchSetTheory :: String -> String -> Maybe (IO ())
dispatchSetTheory proofText = ofSetTheorySys (runCalc proofText)

dispatchHOArith :: String -> String -> Maybe (IO ())
dispatchHOArith proofText = ofHigherOrderArithmeticSys (runCalc proofText)

dispatchDefiniteDesc :: String -> String -> Maybe (IO ())
dispatchDefiniteDesc proofText = ofDefiniteDescSys (runCalc proofText)

strip :: String -> String
strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace

presentResults :: Maybe String -> [Either (ProofErrorMessage lex) b] -> IO ()
presentResults mseq ds = do
    let errors = concatMap reportError (zip [1..] ds)
    if null errors
        then do case mseq of
                    Just s  -> putStrLn $ "Proven: " ++ s
                    Nothing -> putStrLn "Proof valid."
                exitSuccess
        else do mapM_ (hPutStrLn stderr) errors
                case mseq of
                    Nothing -> do
                        hPutStrLn stderr "Proof invalid."
                        exitFailure
                    Just s  -> do
                        putStrLn $ "Proven (with warnings): " ++ s
                        exitSuccess

reportError :: (Int, Either (ProofErrorMessage lex) a) -> [String]
reportError (_, Right _) = []
reportError (_, Left (NoResult _)) = []
reportError (_, Left (NoParse err ln)) =
    ["Line " ++ show ln ++ ", column " ++ show (sourceColumn (errorPos err))
     ++ ": parse error: "
     ++ showErrorMessages "or" "unknown" "expecting" "unexpected" "end of input"
            (errorMessages err)]
reportError (_, Left (NoUnify _ ln)) =
    ["Line " ++ show ln ++ ": could not unify"]
reportError (_, Left (GenericError msg ln)) =
    ["Line " ++ show ln ++ ": " ++ msg]

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
    ]

definiteDescSystems :: [String]
definiteDescSystems =
    [ "gamutNDDesc"
    ]
