{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.FosterAndLaursen
    ( parseFosterAndLaursenTFLCore, FosterAndLaursenTFLCore(..)
    , parseFosterAndLaursenTFL, FosterAndLaursenTFL(..)
    , fosterAndLaursenTFL2019Calc, fosterAndLaursenTFLCalc, fosterAndLaursenTFLCoreCalc
    , fosterAndLaursenNotation) where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.Util.LanguageClasses

{-| A system for propositional logic resembling the basic proof system TFL
from the Calgary Remix of Forall x book
-}

data FosterAndLaursenTFLCore = ConjIntro  | As
                                | ConjElim1  | ConjElim2
                                | DisjIntro1 | DisjIntro2
                                | DisjElim1  | DisjElim2
                                | DisjElim3  | DisjElim4
                                | CondIntro1 | CondIntro2
                                | CondElim
                                | BicoIntro1 | BicoIntro2
                                | BicoIntro3 | BicoIntro4
                                | BicoElim1  | BicoElim2
                                | NegeIntro1 | NegeIntro2
                                | NegeElim   | ContElim 
                                | Indirect1  | Indirect2
                                | Reiterate
                                | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
                                deriving (Eq)

data FosterAndLaursenTFL = Core FosterAndLaursenTFLCore
                            | ModTollens   | DoubleNegElim  
                            | DoubleNegIntro
                            | Lem1         | Lem2
                            | Lem3         | Lem4
                            | DeMorgan1    | DeMorgan2
                            | DeMorgan3    | DeMorgan4
                            | NegBicoDist1 | NegBicoDist2 
                            | NegBicoDist3 | NegBicoDist4
                            | BicoMT1      | BicoMT2
                            deriving (Eq)
                            --skipping derived rules for now

instance Show FosterAndLaursenTFLCore where
        show ConjIntro    = "∧I"
        show ConjElim1    = "∧E"
        show ConjElim2    = "∧E"
        show NegeIntro1   = "¬I"
        show NegeIntro2   = "¬I"
        show NegeElim     = "¬E"
        show Indirect1    = "IP"
        show Indirect2    = "IP"
        show CondIntro1   = "→I"
        show CondIntro2   = "→I"
        show CondElim     = "→E"
        show ContElim     = "⊥E"
        show DisjElim1    = "∨E"
        show DisjElim2    = "∨E"
        show DisjElim3    = "∨E"
        show DisjElim4    = "∨E"
        show DisjIntro1   = "∨I"
        show DisjIntro2   = "∨I"
        show BicoIntro1   = "↔I"
        show BicoIntro2   = "↔I"
        show BicoIntro3   = "↔I"
        show BicoIntro4   = "↔I"
        show BicoElim1    = "↔E"
        show BicoElim2    = "↔E"
        show Reiterate    = "R"
        show As           = "AS"
        show (Pr _)       = "PR"

instance Show FosterAndLaursenTFL where
        show (Core x)     = show x
        show ModTollens   = "MT"
        show DoubleNegElim = "DNE"
        show DoubleNegIntro= "DNI"
        show Lem1         = "LEM"
        show Lem2         = "LEM"
        show Lem3         = "LEM"
        show Lem4         = "LEM"
        show DeMorgan1    = "DeM"
        show DeMorgan2    = "DeM"
        show DeMorgan3    = "DeM"
        show DeMorgan4    = "DeM"
        show NegBicoDist1 = "NBD"
        show NegBicoDist2 = "NBD"
        show NegBicoDist3 = "NBD"
        show NegBicoDist4 = "NBD"
        show BicoMT1      = "BMT"
        show BicoMT2      = "BMT"

instance Inference FosterAndLaursenTFLCore PurePropLexicon (Form Bool) where
        ruleOf ConjIntro    = adjunction
        ruleOf ConjElim1    = simplificationVariations !! 0
        ruleOf ConjElim2    = simplificationVariations !! 1
        ruleOf NegeIntro1   = constructiveFalsumReductioVariations !! 0
        ruleOf NegeIntro2   = constructiveFalsumReductioVariations !! 1
        ruleOf NegeElim     = falsumIntroduction
        ruleOf Indirect1    = nonConstructiveFalsumReductioVariations !! 0
        ruleOf Indirect2    = nonConstructiveFalsumReductioVariations !! 1
        ruleOf CondIntro1   = conditionalProofVariations !! 0
        ruleOf CondIntro2   = conditionalProofVariations !! 1
        ruleOf CondElim     = modusPonens
        ruleOf ContElim     = falsumElimination
        ruleOf DisjIntro1   = additionVariations !! 0
        ruleOf DisjIntro2   = additionVariations !! 1 
        ruleOf DisjElim1    = proofByCasesVariations !! 0
        ruleOf DisjElim2    = proofByCasesVariations !! 1
        ruleOf DisjElim3    = proofByCasesVariations !! 2
        ruleOf DisjElim4    = proofByCasesVariations !! 3
        ruleOf BicoIntro1   = biconditionalProofVariations !! 0
        ruleOf BicoIntro2   = biconditionalProofVariations !! 1
        ruleOf BicoIntro3   = biconditionalProofVariations !! 2
        ruleOf BicoIntro4   = biconditionalProofVariations !! 3
        ruleOf BicoElim1    = biconditionalPonensVariations !! 0
        ruleOf BicoElim2    = biconditionalPonensVariations !! 1
        ruleOf Reiterate    = identityRule
        ruleOf As           = axiom
        ruleOf (Pr _)       = axiom

        indirectInference x
            | x `elem` [ DisjElim1, DisjElim2, DisjElim3, DisjElim4
                       , CondIntro1, CondIntro2 , BicoIntro1, BicoIntro2
                       , BicoIntro3, BicoIntro4, NegeIntro1, NegeIntro2
                       , Indirect1, Indirect2 ] = Just PolyProof
            | otherwise = Nothing

        isAssumption As = True
        isAssumption _  = False

        isPremise (Pr _) = True
        isPremise _  = False

        globalRestriction (Left ded) n CondIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n CondIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n BicoIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n BicoIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n BicoIntro3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n BicoIntro4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n DisjElim1 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n DisjElim2 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n DisjElim3 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n DisjElim4 = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n NegeIntro1 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n NegeIntro2 = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n Indirect1 = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction (Left ded) n Indirect2 = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

instance Inference FosterAndLaursenTFL PurePropLexicon (Form Bool) where
        ruleOf (Core x)   = ruleOf x
        ruleOf ModTollens = modusTollens
        ruleOf DoubleNegElim  = doubleNegationElimination
        ruleOf DoubleNegIntro = doubleNegationIntroduction
        ruleOf Lem1       = tertiumNonDaturVariations !! 0 
        ruleOf Lem2       = tertiumNonDaturVariations !! 1
        ruleOf Lem3       = tertiumNonDaturVariations !! 2
        ruleOf Lem4       = tertiumNonDaturVariations !! 3
        ruleOf DeMorgan1  = deMorgansLaws !! 0
        ruleOf DeMorgan2  = deMorgansLaws !! 1
        ruleOf DeMorgan3  = deMorgansLaws !! 2
        ruleOf DeMorgan4  = deMorgansLaws !! 3
        ruleOf NegBicoDist1 = negatedBiconditionalVariations !! 0
        ruleOf NegBicoDist2 = negatedBiconditionalVariations !! 1
        ruleOf NegBicoDist3 = negatedBiconditionalVariations' !! 0
        ruleOf NegBicoDist4 = negatedBiconditionalVariations' !! 1
        ruleOf BicoMT1    = biconditionalTollensVariations !! 0
        ruleOf BicoMT2    = biconditionalTollensVariations !! 1

        indirectInference (Core x) = indirectInference x
        indirectInference x
            | x `elem` [Lem1,Lem2,Lem3,Lem4] = Just (PolyTypedProof 2 (ProofType 1 1))
            | otherwise = Nothing

        globalRestriction (Left ded) n (Core CondIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (Core CondIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
        globalRestriction (Left ded) n (Core BicoIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core BicoIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core BicoIntro3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core BicoIntro4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
        globalRestriction (Left ded) n (Core DisjElim1) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core DisjElim2) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core DisjElim3) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core DisjElim4) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
        globalRestriction (Left ded) n (Core NegeIntro1) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (Core NegeIntro2) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
        globalRestriction (Left ded) n (Core Indirect1) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction (Left ded) n (Core Indirect2) = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
        globalRestriction _ _ _ = Nothing

        isAssumption (Core x) = isAssumption x
        isAssumption _  = False

        isPremise (Core x) = isAssumption x
        isPremise _  = False

        restriction (Core x) = restriction x
        restriction _ = Nothing

parseFosterAndLaursenTFLCore :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [FosterAndLaursenTFLCore]
parseFosterAndLaursenTFLCore rtc = do r <- choice (map (try . string) [ "AS","PR","&I","/\\I", "∧I", "^I", "&E","/\\E","∧E","^E","~I","-I", "¬I"
                                                                   , "~E","-E", "¬E","IP","PBC","->I", ">I", "=>I", "→I","->E", "=>E", ">E", "→E", "⊥E", "_|_E", "X"
                                                                   , "vI","\\/I", "|I", "∨I", "vE","\\/E", "|E", "∨E","<->I", "↔I","<->E", "↔E"
                                                                   , "R"])
                                      case r of
                                         r | r == "AS"   -> return [As]
                                           | r == "PR" -> return [Pr (problemPremises rtc)]
                                           | r `elem` ["&I","/\\I","∧I","^I"] -> return [ConjIntro]
                                           | r `elem` ["&E","/\\E","∧E","^E"] -> return [ConjElim1, ConjElim2]
                                           | r `elem` ["~I","¬I","-I"]   -> return [NegeIntro1, NegeIntro2]
                                           | r `elem` ["~E","¬E","-E"]   -> return [NegeElim]
                                           | r `elem` ["IP","PBC"]  -> return [Indirect1, Indirect2]
                                           | r `elem` ["->I", ">I", "=>I", "→I"] -> return [CondIntro1,CondIntro2]
                                           | r `elem` ["->E", ">E", "=>E", "→E"]  -> return [CondElim]
                                           | r `elem` ["X", "_|_E", "⊥E"]    -> return [ContElim]
                                           | r `elem` ["∨I","vI", "|I", "\\/I"] -> return [DisjIntro1, DisjIntro2]
                                           | r `elem` ["∨E","vE", "|E", "\\/E"] -> return [DisjElim1, DisjElim2, DisjElim3, DisjElim4]
                                           | r `elem` ["<->I","↔I"] -> return [BicoIntro1, BicoIntro2, BicoIntro3, BicoIntro4]
                                           | r `elem` ["<->E","↔E"]   -> return [BicoElim1, BicoElim2]
                                           | r == "R" -> return [Reiterate]

parseFosterAndLaursenTFL :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [FosterAndLaursenTFL]
parseFosterAndLaursenTFL rtc = try parseExt <|> (map Core <$> parseFosterAndLaursenTFLCore rtc)
        where parseExt = do r <- choice (map (try . string) ["MT","DNE","~~E","¬¬E","--E", "DNI", "~~I","¬¬I","--I","LEM","DeM", "NBD", "BMT"])
                            case r of
                               r | r == "MT"   -> return [ModTollens]
                                 | r `elem` ["DNE","~~E", "¬¬E","--E"] -> return [DoubleNegElim]
                                 | r `elem` ["DNI","~~I","¬¬I","--I"] -> return [DoubleNegIntro]
                                 | r == "LEM"  -> return [Lem1,Lem2,Lem3,Lem4]
                                 | r == "DeM"   -> return [DeMorgan1,DeMorgan2,DeMorgan3,DeMorgan4]
                                 | r == "NBD"  -> return [NegBicoDist1, NegBicoDist2, NegBicoDist3, NegBicoDist4]
                                 | r == "BMT"  -> return [BicoMT1, BicoMT2]

parseFosterAndLaursenTFLCoreProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine FosterAndLaursenTFLCore PurePropLexicon (Form Bool)]
parseFosterAndLaursenTFLCoreProof rtc = toDeductionFitch (parseFosterAndLaursenTFLCore rtc) (purePropFormulaParser fosterLaursenOpts) 

parseFosterAndLaursenTFLProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine FosterAndLaursenTFL PurePropLexicon (Form Bool)]
parseFosterAndLaursenTFLProof rtc = toDeductionFitch (parseFosterAndLaursenTFL rtc) (purePropFormulaParser fosterLaursenOpts)

parseFosterAndLaursenTFL2019Proof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine FosterAndLaursenTFLCore PurePropLexicon (Form Bool)]
parseFosterAndLaursenTFL2019Proof rtc = toDeductionFitch (parseFosterAndLaursenTFLCore rtc) (purePropFormulaParser fosterLaursenOpts)

fosterAndLaursenNotation :: String -> String 
fosterAndLaursenNotation x = case runParser altParser 0 "" x of
                        Left e -> show e
                        Right s -> s
    where altParser = do s <- try handleAtom <|> fallback
                         rest <- (eof >> return "") <|> altParser
                         return $ s ++ rest
          handleAtom = do c <- oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <* char '('
                          args <- oneOf "abcdefghijklmnopqrstuvwxyz" `sepBy` char ','
                          char ')'
                          return $ c:args
          fallback = do c <- anyChar 
                        return [c]

fosterAndLaursenTFLCoreCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseFosterAndLaursenTFLCoreProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser fosterLaursenOpts)
    , ndParseForm = purePropFormulaParser fosterLaursenOpts
    , ndNotation = fosterAndLaursenNotation
    }

fosterAndLaursenTFLCalc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseFosterAndLaursenTFLProof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser fosterLaursenOpts)
    , ndParseForm = purePropFormulaParser fosterLaursenOpts
    , ndNotation = fosterAndLaursenNotation
    }

fosterAndLaursenTFL2019Calc = mkNDCalc 
    { ndRenderer = FitchStyle StandardFitch
    , ndParseProof = parseFosterAndLaursenTFL2019Proof
    , ndProcessLine = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZach2019Opts)
    , ndParseForm = purePropFormulaParser thomasBolducZach2019Opts
    , ndNotation = dropOuterParens
    }
