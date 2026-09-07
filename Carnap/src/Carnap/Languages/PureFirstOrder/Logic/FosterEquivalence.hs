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
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint, identityRule)
import Carnap.Languages.PureFirstOrder.Logic.Rules
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
        -- Delegate all propositional rules directly to FosterPropEq
        ruleOf (Prop p) = ruleOf p
        -- Quantifier and First-Order rules
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
        ruleOf VR  = identityRule
        ruleOf (Pr _) = axiom
        
        restriction (Pr prems) = Just (premConstraint prems)
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