{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PureFirstOrder.Logic.FosterEquivalence 
    ( fosterFOLEqCalc
    , parseFosterFOLEq
    , FosterFOLEq(..)
    ) where

import Text.Parsec
import Data.Char (toUpper, toLower)
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.PureFirstOrder.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PureFirstOrder.Logic.Rules
import qualified Carnap.Languages.PurePropositional.Logic.Rules as PropRules
import qualified Carnap.Languages.PurePropositional.Logic.FosterEquivalence as Prop

data FosterFOLEq = Prop Prop.FosterPropEq
                 | QN1  | QN2  | QN3  | QN4 
                 | QD1  | QD2  | QD3  | QD4 
                 | QSA1 | QSA2 | QSA3 | QSA4
                 | QSA5 | QSA6 | QSA7 | QSA8
                 | QSA9 | QSA10 | QSA11 | QSA12
                 | QSE1 | QSE2 | QSE3 | QSE4
                 | QSE5 | QSE6 | QSE7 | QSE8
                 | QSE9 | QSE10 | QSE11 | QSE12
                 | QXE  | QXA
                 | VR   | Pr (Maybe [(ClassicalSequentOver PureLexiconFOL (Sequent (Form Bool)))])
    deriving (Eq)

instance Show FosterFOLEq where
        show (Prop x) = show x
        show QN1  = "QN"
        show QN2  = "QN"
        show QN3  = "QN"
        show QN4  = "QN"
        show QD1  = "QD" 
        show QD2  = "QD"
        show QD3  = "QD"
        show QD4  = "QD"
        show QSA1 = "QSA" 
        show QSA2 = "QSA"
        show QSA3 = "QSA"
        show QSA4 = "QSA"
        show QSA5 = "QSA"
        show QSA6 = "QSA"
        show QSA7 = "QSA"
        show QSA8 = "QSA"
        show QSA9 = "QSA"
        show QSA10 = "QSA"
        show QSA11 = "QSA"
        show QSA12 = "QSA"
        show QSE1 = "QSE" 
        show QSE2 = "QSE"
        show QSE3 = "QSE"
        show QSE4 = "QSE"
        show QSE5 = "QSE"
        show QSE6 = "QSE"
        show QSE7 = "QSE"
        show QSE8 = "QSE"
        show QSE9 = "QSE"
        show QSE10 = "QSE"
        show QSE11 = "QSE"
        show QSE12 = "QSE"
        show QXE   = "QX"
        show QXA   = "QX"
        show VR    = "VR"
        show (Pr _) = "LHS"

instance Inference FosterFOLEq PureLexiconFOL (Form Bool) where
        ruleOf (Prop Prop.AndComm) = PropRules.andCommutativity !! 0
        ruleOf (Prop Prop.CommAnd) = PropRules.andCommutativity !! 1
        ruleOf (Prop Prop.OrComm)  = PropRules.orCommutativity !! 0
        ruleOf (Prop Prop.CommOr)  = PropRules.orCommutativity !! 1
        ruleOf (Prop Prop.IffComm) = PropRules.iffCommutativity !! 0 
        ruleOf (Prop Prop.CommIff) = PropRules.iffCommutativity !! 1
        ruleOf (Prop Prop.DNRep)   = PropRules.doubleNegation !! 0
        ruleOf (Prop Prop.RepDN)   = PropRules.doubleNegation !! 1
        ruleOf (Prop Prop.MCRep)   = PropRules.materialConditional !! 0
        ruleOf (Prop Prop.RepMC)   = PropRules.materialConditional !! 1
        ruleOf (Prop Prop.MCRep2)  = PropRules.materialConditional !! 2
        ruleOf (Prop Prop.RepMC2)  = PropRules.materialConditional !! 3
        ruleOf (Prop Prop.BiExRep) = PropRules.biconditionalExchange !! 0
        ruleOf (Prop Prop.AndAssoc) = PropRules.andAssociativity !! 0
        ruleOf (Prop Prop.AssocAnd) = PropRules.andAssociativity !! 1
        ruleOf (Prop Prop.OrAssoc)  = PropRules.orAssociativity !! 0 
        ruleOf (Prop Prop.AssocOr)  = PropRules.orAssociativity !! 1
        ruleOf (Prop Prop.AndIdem)  = PropRules.andIdempotence !! 0
        ruleOf (Prop Prop.IdemAnd)  = PropRules.andIdempotence !! 1
        ruleOf (Prop Prop.OrIdem)   = PropRules.orIdempotence !! 0
        ruleOf (Prop Prop.IdemOr)   = PropRules.orIdempotence !! 1
        ruleOf (Prop Prop.OrDistL)  = PropRules.orDistributivity !! 0
        ruleOf (Prop Prop.DistOrL)  = PropRules.orDistributivity !! 1
        ruleOf (Prop Prop.OrDistR)  = PropRules.orDistributivity !! 2
        ruleOf (Prop Prop.DistOrR)  = PropRules.orDistributivity !! 3
        ruleOf (Prop Prop.AndDistL) = PropRules.andDistributivity !! 0
        ruleOf (Prop Prop.DistAndL) = PropRules.andDistributivity !! 1
        ruleOf (Prop Prop.AndDistR) = PropRules.andDistributivity !! 2
        ruleOf (Prop Prop.DistAndR) = PropRules.andDistributivity !! 3
        ruleOf (Prop Prop.AndAbsorb1) = PropRules.andAbsorption !! 0
        ruleOf (Prop Prop.AbsorbAnd1) = PropRules.andAbsorption !! 1
        ruleOf (Prop Prop.AndAbsorb2) = PropRules.andAbsorption !! 2
        ruleOf (Prop Prop.AbsorbAnd2) = PropRules.andAbsorption !! 3
        ruleOf (Prop Prop.AndAbsorb3) = PropRules.andAbsorption !! 4
        ruleOf (Prop Prop.AbsorbAnd3) = PropRules.andAbsorption !! 5
        ruleOf (Prop Prop.AndAbsorb4) = PropRules.andAbsorption !! 6
        ruleOf (Prop Prop.AbsorbAnd4) = PropRules.andAbsorption !! 7
        ruleOf (Prop Prop.OrAbsorb1)  = PropRules.orAbsorption !! 0
        ruleOf (Prop Prop.AbsorbOr1)  = PropRules.orAbsorption !! 1
        ruleOf (Prop Prop.OrAbsorb2)  = PropRules.orAbsorption !! 2
        ruleOf (Prop Prop.AbsorbOr2)  = PropRules.orAbsorption !! 3
        ruleOf (Prop Prop.OrAbsorb3)  = PropRules.orAbsorption !! 4
        ruleOf (Prop Prop.AbsorbOr3)  = PropRules.orAbsorption !! 5
        ruleOf (Prop Prop.OrAbsorb4)  = PropRules.orAbsorption !! 6
        ruleOf (Prop Prop.AbsorbOr4)  = PropRules.orAbsorption !! 7
        ruleOf (Prop Prop.NCRep)   = PropRules.negatedConditional !! 0
        ruleOf (Prop Prop.RepNC)   = PropRules.negatedConditional !! 1
        ruleOf (Prop Prop.RepBiEx) = PropRules.biconditionalExchange !! 1
        ruleOf (Prop Prop.DM1)     = PropRules.deMorgansLaws !! 0
        ruleOf (Prop Prop.DM2)     = PropRules.deMorgansLaws !! 1
        ruleOf (Prop Prop.DM3)     = PropRules.deMorgansLaws !! 2
        ruleOf (Prop Prop.DM4)     = PropRules.deMorgansLaws !! 3
        ruleOf (Prop Prop.AndUnit1)    = PropRules.andUnit !! 0
        ruleOf (Prop Prop.RepAndUnit1) = PropRules.andUnit !! 1
        ruleOf (Prop Prop.AndUnit2)    = PropRules.andUnit !! 2
        ruleOf (Prop Prop.RepAndUnit2) = PropRules.andUnit !! 3
        ruleOf (Prop Prop.OrUnit1)     = PropRules.orUnit !! 0
        ruleOf (Prop Prop.RepOrUnit1)  = PropRules.orUnit !! 1
        ruleOf (Prop Prop.OrUnit2)     = PropRules.orUnit !! 2
        ruleOf (Prop Prop.RepOrUnit2)  = PropRules.orUnit !! 3
        ruleOf (Prop Prop.AndZero1)    = PropRules.andZero !! 0
        ruleOf (Prop Prop.RepAndZero1) = PropRules.andZero !! 1
        ruleOf (Prop Prop.AndZero2)    = PropRules.andZero !! 2
        ruleOf (Prop Prop.RepAndZero2) = PropRules.andZero !! 3
        ruleOf (Prop Prop.OrZero1)     = PropRules.orZero !! 0
        ruleOf (Prop Prop.RepOrZero1)  = PropRules.orZero !! 1
        ruleOf (Prop Prop.OrZero2)     = PropRules.orZero !! 2
        ruleOf (Prop Prop.RepOrZero2)  = PropRules.orZero !! 3
        ruleOf (Prop Prop.LEM)     = PropRules.lawOfExcludedMiddle !! 0
        ruleOf (Prop Prop.RepLEM)  = PropRules.lawOfExcludedMiddle !! 1
        ruleOf (Prop Prop.LEM2)    = PropRules.lawOfExcludedMiddle !! 2
        ruleOf (Prop Prop.RepLEM2) = PropRules.lawOfExcludedMiddle !! 3
        ruleOf (Prop Prop.LC)      = PropRules.lawOfContradiction !! 0
        ruleOf (Prop Prop.RepLC)   = PropRules.lawOfContradiction !! 1
        ruleOf (Prop Prop.LC2)     = PropRules.lawOfContradiction !! 2
        ruleOf (Prop Prop.RepLC2)  = PropRules.lawOfContradiction !! 3        
        ruleOf (Prop Prop.NegTop)    = PropRules.negatedConstants !! 0
        ruleOf (Prop Prop.RepNegTop) = PropRules.negatedConstants !! 1
        ruleOf (Prop Prop.NegBot)    = PropRules.negatedConstants !! 2
        ruleOf (Prop Prop.RepNegBot) = PropRules.negatedConstants !! 3
        ruleOf QN1 = quantifierNegationReplace !! 0
        ruleOf QN2 = quantifierNegationReplace !! 1
        ruleOf QN3 = quantifierNegationReplace !! 2
        ruleOf QN4 = quantifierNegationReplace !! 3
        ruleOf QD1 = quantifierDistribution !! 0 
        ruleOf QD2 = quantifierDistribution !! 1
        ruleOf QD3 = quantifierDistribution !! 2 
        ruleOf QD4 = quantifierDistribution !! 3 
        ruleOf QSA1 = rulesOfPassage !! 2
        ruleOf QSA2 = rulesOfPassage !! 3 
        ruleOf QSA3 = rulesOfPassage !! 6 
        ruleOf QSA4 = rulesOfPassage !! 7 
        ruleOf QSA5 = rulesOfPassage !! 10 
        ruleOf QSA6 = rulesOfPassage !! 11 
        ruleOf QSA7 = rulesOfPassage !! 14 
        ruleOf QSA8 = rulesOfPassage !! 15 
        ruleOf QSA9 = conditionalRulesOfPassage !! 0
        ruleOf QSA10 = conditionalRulesOfPassage !! 1
        ruleOf QSA11 = conditionalRulesOfPassage !! 4
        ruleOf QSA12 = conditionalRulesOfPassage !! 5
        ruleOf QSE1 = rulesOfPassage !! 0
        ruleOf QSE2 = rulesOfPassage !! 1 
        ruleOf QSE3 = rulesOfPassage !! 4 
        ruleOf QSE4 = rulesOfPassage !! 5 
        ruleOf QSE5 = rulesOfPassage !! 8
        ruleOf QSE6 = rulesOfPassage !! 9
        ruleOf QSE7 = rulesOfPassage !! 12
        ruleOf QSE8 = rulesOfPassage !! 13 
        ruleOf QSE9 = conditionalRulesOfPassage !! 2
        ruleOf QSE10 = conditionalRulesOfPassage !! 3
        ruleOf QSE11 = conditionalRulesOfPassage !! 6
        ruleOf QSE12 = conditionalRulesOfPassage !! 7
        ruleOf QXE = quantifierExchange !! 0
        ruleOf QXA = quantifierExchange !! 2
        ruleOf VR  = PropRules.identityRule
        ruleOf (Pr _) = PropRules.axiom

        restriction (Pr prems) = Just (PropRules.premConstraint prems)
        restriction _ = Nothing

        isPremise (Pr _) = True
        isPremise _ = False

parseFosterFOLEq :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> Parsec String u [FosterFOLEq]
parseFosterFOLEq rtc = try quantRule <|> try (map Prop <$> propRule)
    where propRule = Prop.parseFosterPropEq defaultRuntimeDeductionConfig
          quantRule = do r <- choice (map (try . caseInsensitiveString) ["QN","QD","QSA","QSE","QX","VR","LHS","PR"])
                         return $ case map toLower r of 
                            "qn"  -> [QN1, QN2, QN3, QN4]
                            "qd"  -> [QD1, QD2, QD3, QD4]
                            "qsa" -> [QSA1, QSA2, QSA3, QSA4, QSA5, QSA6, QSA7, QSA8, QSA9, QSA10, QSA11, QSA12]
                            "qse" -> [QSE1, QSE2, QSE3, QSE4, QSE5, QSE6, QSE7, QSE8, QSE9, QSE10, QSE11, QSE12]
                            "qx"  -> [QXA, QXE]
                            "vr"  -> [VR]
                            "lhs" -> [Pr (problemPremises rtc)]
                            "pr"  -> [Pr (problemPremises rtc)]
          caseInsensitiveChar c = char (toLower c) <|> char (toUpper c)
          caseInsensitiveString s = try (mapM caseInsensitiveChar s) <?> "\"" ++ s ++ "\""

parseFosterFOLEqProof :: RuntimeDeductionConfig PureLexiconFOL (Form Bool) -> String -> [DeductionLine FosterFOLEq PureLexiconFOL (Form Bool)]
parseFosterFOLEqProof ders = toDeductionHilbertImplicit (parseFosterFOLEq ders) thomasBolducAndZachFOL2019FormulaParserStrict

fosterFOLEqCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseFosterFOLEqProof
    , ndProcessLine = hoProcessLineHilbertImplicit
    , ndProcessLineMemo = Just hoProcessLineHilbertImplicitMemo
    , ndParseSeq = parseSeqOver thomasBolducAndZachFOL2019FormulaParserStrict
    , ndParseForm = thomasBolducAndZachFOL2019FormulaParserStrict
    , ndNotation = formatEquationalSeq . dropOuterParens 
    }

formatEquationalSeq :: String -> String
formatEquationalSeq s = case break (== '⊢') s of
    (lhs, '⊢':rhs) -> lhs ++ "≡" ++ rhs
    _ -> s