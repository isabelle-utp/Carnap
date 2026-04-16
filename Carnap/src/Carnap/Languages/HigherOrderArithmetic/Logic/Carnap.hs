{-#LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.HigherOrderArithmetic.Logic.Carnap (hoArithCalc, HOArithLogic(..)) where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Syntax (fogamma)
import Carnap.Languages.HigherOrderArithmetic.Syntax
import Carnap.Languages.HigherOrderArithmetic.Parser
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint)
import Carnap.Languages.PureFirstOrder.Logic (FOLogic(ED1,ED2,UD,UI,EG,QN1,QN2,QN3,QN4,LL1,LL2,ALL1,ALL2,EL1,EL2,ID,SM,SL), parseFOLogic)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.SetTheory.Logic.Rules
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineMontague, hoProcessLineMontagueMemo)
import Carnap.Languages.Util.LanguageClasses
import Text.Parsec

data HOArithLogic = DefU1   | DefI1 | DefP1 | DefC1 | DefC3 | DefID1 | DefID3 | DefSub1
                  | DefU2   | DefI2 | DefP2 | DefC2 | DefC4 | DefID2 | DefID4 | DefSub2
                  | DefES1  | DefES2 | DefES3 | DefES4
                  | DefSep1 | DefSep2 | DefSep3 | DefSep4
                  | FO FOLogic
                  | PR (Maybe [(ClassicalSequentOver UntypedHigherOrderArithLex (Sequent (Form Bool)))])
                  deriving (Eq)

instance Show HOArithLogic where
    show (PR _)   = "PR"
    show (FO x)   = show x
    show DefU1    = "Def-U"
    show DefU2    = "Def-U"
    show DefI1    = "Def-I"
    show DefI2    = "Def-I"
    show DefC1    = "Def-C"
    show DefC2    = "Def-C"
    show DefC3    = "Def-C"
    show DefC4    = "Def-C"
    show DefID1   = "Def-="
    show DefID2   = "Def-="
    show DefID3   = "Def-="
    show DefID4   = "Def-="
    show DefES1   = "Def-∅"
    show DefES2   = "Def-∅"
    show DefES3   = "Def-∅"
    show DefES4   = "Def-∅"
    show DefP1    = "Def-P"
    show DefP2    = "Def-P"
    show DefSub1  = "Def-S"
    show DefSub2  = "Def-S"
    show DefSep1  = "Def-{}"
    show DefSep2  = "Def-{}"
    show DefSep3  = "Def-{}"
    show DefSep4  = "Def-{}"

instance Inference HOArithLogic UntypedHigherOrderArithLex (Form Bool) where
    ruleOf (PR _)   = axiom
    ruleOf DefU1    = unpackUnion !! 0
    ruleOf DefU2    = unpackUnion !! 1
    ruleOf DefI1    = unpackIntersection !! 0
    ruleOf DefI2    = unpackIntersection !! 1
    ruleOf DefC1    = unpackComplement !! 0
    ruleOf DefC2    = unpackComplement !! 1
    ruleOf DefC3    = unpackComplement !! 2
    ruleOf DefC4    = unpackComplement !! 3
    ruleOf DefID1   = unpackEquality !! 0
    ruleOf DefID2   = unpackEquality !! 1
    ruleOf DefID3   = unpackEquality !! 2
    ruleOf DefID4   = unpackEquality !! 3
    ruleOf DefES1   = unpackEmptySet !! 0
    ruleOf DefES2   = unpackEmptySet !! 1
    ruleOf DefES3   = unpackEmptySet !! 2
    ruleOf DefES4   = unpackEmptySet !! 3
    ruleOf DefSub1  = unpackSubset !! 0
    ruleOf DefSub2  = unpackSubset !! 1
    ruleOf DefP1    = unpackPowerset !! 0
    ruleOf DefP2    = unpackPowerset !! 1
    ruleOf DefSep1  = unpackSeparation !! 0
    ruleOf DefSep2  = unpackSeparation !! 1
    ruleOf DefSep3  = unpackSeparation !! 2
    ruleOf DefSep4  = unpackSeparation !! 3
    ruleOf (FO UI  ) = universalInstantiation
    ruleOf (FO EG  ) = existentialGeneralization
    ruleOf (FO UD  ) = universalGeneralization
    ruleOf (FO ED1 ) = existentialDerivation !! 0
    ruleOf (FO ED2 ) = existentialDerivation !! 1
    ruleOf (FO QN1 ) = quantifierNegation !! 0
    ruleOf (FO QN2 ) = quantifierNegation !! 1
    ruleOf (FO QN3 ) = quantifierNegation !! 2
    ruleOf (FO QN4 ) = quantifierNegation !! 3
    ruleOf (FO LL1 ) = leibnizLawVariations !! 0
    ruleOf (FO LL2 ) = leibnizLawVariations !! 1
    ruleOf (FO ALL1) = antiLeibnizLawVariations !! 0
    ruleOf (FO ALL2) = antiLeibnizLawVariations !! 1
    ruleOf (FO EL1 ) = euclidsLawVariations !! 0
    ruleOf (FO EL2 ) = euclidsLawVariations !! 1
    ruleOf (FO ID  ) = eqReflexivity
    ruleOf (FO SM  ) = eqSymmetry

    premisesOf (FO (SL x)) = map liftSequent (premisesOf x)
    premisesOf r = upperSequents (ruleOf r)

    conclusionOf (FO (SL x)) = liftSequent (conclusionOf x)
    conclusionOf r = lowerSequent (ruleOf r)

    restriction (PR prems) = Just (premConstraint prems)
    restriction (FO UD)    = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1))
        where stau = liftToSequent tau
    restriction (FO ED1)   = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction (FO ED2)   = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction _ = Nothing

    indirectInference (FO x) = indirectInference x
    indirectInference _ = Nothing

parseHOArithLogic :: RuntimeDeductionConfig UntypedHigherOrderArithLex (Form Bool) -> Parsec String u [HOArithLogic]
parseHOArithLogic rtc = try hoArithRule <|> liftFO
    where liftFO = map FO <$> parseFOLogic defaultRuntimeDeductionConfig
          hoArithRule = do
              r <- choice (map (try . string) ["PR","Def-U","Def-I","Def-C","Def-P","Def-S","Def-=","Def-\8709","Def-{}"])
              return $ case r of
                  "PR"     -> [PR $ problemPremises rtc]
                  "Def-U"  -> [DefU1, DefU2]
                  "Def-I"  -> [DefI1, DefI2]
                  "Def-C"  -> [DefC1, DefC2, DefC3, DefC4]
                  "Def-S"  -> [DefSub1, DefSub2]
                  "Def-P"  -> [DefP1, DefP2]
                  "Def-="  -> [DefID1, DefID2, DefID3, DefID4]
                  "Def-\8709" -> [DefES1, DefES2, DefES3, DefES4]
                  _        -> [DefSep1, DefSep2, DefSep3, DefSep4]

parseHOArithProof :: RuntimeDeductionConfig UntypedHigherOrderArithLex (Form Bool)
                  -> String -> [DeductionLine HOArithLogic UntypedHigherOrderArithLex (Form Bool)]
parseHOArithProof rtc = toDeductionMontague (parseHOArithLogic rtc) untypedHigherOrderArithmeticMontagueParser

hoArithCalc :: NaturalDeductionCalc HOArithLogic UntypedHigherOrderArithLex (Form Bool)
hoArithCalc = mkNDCalc
    { ndRenderer = MontagueStyle
    , ndParseProof = parseHOArithProof
    , ndProcessLine = hoProcessLineMontague
    , ndProcessLineMemo = Just hoProcessLineMontagueMemo
    , ndParseForm = untypedHigherOrderArithmeticMontagueParser
    , ndParseSeq = parseSeqOver untypedHigherOrderArithmeticMontagueParser
    }
