{-#LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
module Carnap.Languages.HOArithSum.Logic.FosterLaursen
    ( hoArithSumFLCalc
    , HOArithSumFL(..)
    , parseHOArithSumFL
    ) where

import Text.Parsec
import Carnap.Core.Data.Types
import Carnap.Core.Unification.Unification (applySub)
import Carnap.Languages.HOArithSum.Syntax
import Carnap.Languages.HOArithSum.Parser
import Carnap.Languages.HOArithSum.Util (decidePolyEq)
import Carnap.Languages.PureFirstOrder.Syntax (fogamma)
import Carnap.Languages.PureFirstOrder.Logic
    (FOLogic(ED1,ED2,UD,UI,EG,QN1,QN2,QN3,QN4,LL1,LL2,ALL1,ALL2,EL1,EL2,ID,SM,SL), parseFOLogic)
import Carnap.Languages.PureFirstOrder.Logic.Rules
import Carnap.Languages.SetTheory.Logic.Rules
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker (hoProcessLineFitch, hoProcessLineFitchMemo)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Core.Data.Optics (binaryOpPrism)
import qualified Control.Lens
import Control.Lens (preview)

------------------------------------------------------------
-- Rule type
------------------------------------------------------------

data HOArithSumFL
    = FO FOLogic
    -- set-theory definitional unpacks (from HOArith)
    | DefU1   | DefU2  | DefI1 | DefI2  | DefP1 | DefP2
    | DefC1   | DefC2  | DefC3 | DefC4
    | DefID1  | DefID2 | DefID3 | DefID4
    | DefES1  | DefES2 | DefES3 | DefES4
    | DefSub1 | DefSub2
    | DefSep1 | DefSep2 | DefSep3 | DefSep4
    -- new arithmetic / sum rules
    | Induction | InductionPlus
    | PolyEq
    | SumZero
    | SumSucc | SumPlus
    -- premise
    | Pr (Maybe [(ClassicalSequentOver HOArithSumLex (Sequent (Form Bool)))])
    -- subproof assumption
    | As
    deriving Eq

instance Show HOArithSumFL where
    show (FO LL1)  = "EQ"; show (FO LL2)  = "EQ"
    show (FO ALL1) = "EQ"; show (FO ALL2) = "EQ"
    show (FO x)    = show x
    show (Pr _)    = "PR"
    show DefU1     = "Def-U";  show DefU2     = "Def-U"
    show DefI1     = "Def-I";  show DefI2     = "Def-I"
    show DefC1     = "Def-C";  show DefC2     = "Def-C"
    show DefC3     = "Def-C";  show DefC4     = "Def-C"
    show DefID1    = "Def-=";  show DefID2    = "Def-="
    show DefID3    = "Def-=";  show DefID4    = "Def-="
    show DefES1    = "Def-\8709"; show DefES2 = "Def-\8709"
    show DefES3    = "Def-\8709"; show DefES4 = "Def-\8709"
    show DefP1     = "Def-P";  show DefP2     = "Def-P"
    show DefSub1   = "Def-S";  show DefSub2   = "Def-S"
    show DefSep1   = "Def-{}"; show DefSep2   = "Def-{}"
    show DefSep3   = "Def-{}"; show DefSep4   = "Def-{}"
    show Induction = "Ind"; show InductionPlus = "Ind"
    show PolyEq    = "Poly"
    show SumZero   = "ΣZ"
    show SumSucc   = "ΣS"; show SumPlus = "ΣS"
    show As        = "AS"

------------------------------------------------------------
-- Schematic rules for Σ and induction
------------------------------------------------------------

-- An induction rule of the Fitch-style form:
--      P(0)
--      [t ⊢  P(Suc t)]   (subproof from assumption P(t), eigenvar t)
--      ────────────────
--           ∀x. P(x)
inductionRule :: SequentRule HOArithSumLex (Form Bool)
inductionRule =
    [ GammaV 1 :|-: SS (phi 1 arithZero)
    , GammaV 2 :+: SA (phi 1 (taun 1)) :|-: SS (phi 1 (arithSucc (taun 1)))
    , SA (phi 1 (taun 1)) :|-: SS (phi 1 (taun 1))
    ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lall "v" (phi 1))

-- The same rule with the successor step spelled "t + 1" instead of "t'",
-- so that proofs can avoid successor notation entirely.
inductionPlusRule :: SequentRule HOArithSumLex (Form Bool)
inductionPlusRule =
    [ GammaV 1 :|-: SS (phi 1 arithZero)
    , GammaV 2 :+: SA (phi 1 (taun 1)) :|-: SS (phi 1 (taun 1 `arithPlus` arithOne))
    , SA (phi 1 (taun 1)) :|-: SS (phi 1 (taun 1))
    ] ∴ GammaV 1 :+: GammaV 2 :|-: SS (lall "v" (phi 1))

-- A no-premise schematic equation; the actual decidability check is done
-- in 'globalRestriction' below.
polyEqRule :: SequentRule HOArithSumLex (Form Bool)
polyEqRule = [] ∴ Top :|-: SS (tau `equals` tau')

-- Σi=0..0. θ(i)  =  θ(0)
sumZeroRule :: SequentRule HOArithSumLex (Form Bool)
sumZeroRule = [] ∴ Top :|-: SS
    ( iteratedSum "i" arithZero theta `equals` theta arithZero )

-- Σi=0..Suc(τ). θ(i) = (Σi=0..τ. θ(i)) + θ(Suc τ)
sumSuccRule :: SequentRule HOArithSumLex (Form Bool)
sumSuccRule = [] ∴ Top :|-: SS
    ( iteratedSum "i" (arithSucc tau) theta
      `equals`
      (iteratedSum "i" tau theta `arithPlus` theta (arithSucc tau))
    )

-- Σi=0..τ+1. θ(i) = (Σi=0..τ. θ(i)) + θ(τ+1)
sumPlusRule :: SequentRule HOArithSumLex (Form Bool)
sumPlusRule = [] ∴ Top :|-: SS
    ( iteratedSum "i" (tau `arithPlus` arithOne) theta
      `equals`
      (iteratedSum "i" tau theta `arithPlus` theta (tau `arithPlus` arithOne))
    )

-- The numeral 1, used by the successor-free rule variants.
arithOne :: ClassicalSequentOver HOArithSumLex (Term Int)
arithOne = arithSucc arithZero

------------------------------------------------------------
-- Inference instance
------------------------------------------------------------

instance Inference HOArithSumFL HOArithSumLex (Form Bool) where
    ruleOf (Pr _)    = axiom
    ruleOf As        = axiom
    ruleOf DefU1     = unpackUnion !! 0
    ruleOf DefU2     = unpackUnion !! 1
    ruleOf DefI1     = unpackIntersection !! 0
    ruleOf DefI2     = unpackIntersection !! 1
    ruleOf DefC1     = unpackComplement !! 0
    ruleOf DefC2     = unpackComplement !! 1
    ruleOf DefC3     = unpackComplement !! 2
    ruleOf DefC4     = unpackComplement !! 3
    ruleOf DefID1    = unpackEquality !! 0
    ruleOf DefID2    = unpackEquality !! 1
    ruleOf DefID3    = unpackEquality !! 2
    ruleOf DefID4    = unpackEquality !! 3
    ruleOf DefES1    = unpackEmptySet !! 0
    ruleOf DefES2    = unpackEmptySet !! 1
    ruleOf DefES3    = unpackEmptySet !! 2
    ruleOf DefES4    = unpackEmptySet !! 3
    ruleOf DefSub1   = unpackSubset !! 0
    ruleOf DefSub2   = unpackSubset !! 1
    ruleOf DefP1     = unpackPowerset !! 0
    ruleOf DefP2     = unpackPowerset !! 1
    ruleOf DefSep1   = unpackSeparation !! 0
    ruleOf DefSep2   = unpackSeparation !! 1
    ruleOf DefSep3   = unpackSeparation !! 2
    ruleOf DefSep4   = unpackSeparation !! 3
    ruleOf Induction = inductionRule
    ruleOf InductionPlus = inductionPlusRule
    ruleOf PolyEq    = polyEqRule
    ruleOf SumZero   = sumZeroRule
    ruleOf SumSucc   = sumSuccRule
    ruleOf SumPlus   = sumPlusRule
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

    indirectInference Induction     = Just assumptiveProof
    indirectInference InductionPlus = Just assumptiveProof
    indirectInference (FO x)    = indirectInference x
    indirectInference _         = Nothing

    restriction (Pr prems)  = Just (premConstraint prems)
    restriction (FO UD)     = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1))
        where stau = liftToSequent tau
    restriction (FO ED1)    = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction (FO ED2)    = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction Induction   = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction InductionPlus = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction PolyEq      = Just polyEqConstraint
    restriction _           = Nothing

    -- Fitch-style scope: induction's second premise is a subproof.
    globalRestriction (Left ded) n Induction =
        Just (notAssumedConstraint n ded (taun 1 :: ClassicalSequentOver HOArithSumLex (Term Int)))
    globalRestriction (Left ded) n InductionPlus =
        Just (notAssumedConstraint n ded (taun 1 :: ClassicalSequentOver HOArithSumLex (Term Int)))
    globalRestriction _ _ _ = Nothing

    isAssumption As = True
    isAssumption _  = False
    isPremise (Pr _) = True
    isPremise _      = False

-- | The substitution-aware decidability check for PolyEq.  We walk the
-- conclusion to extract the LHS and RHS of the equation, then run the
-- polynomial decision procedure on the substituted terms.
polyEqConstraint sub =
    case preview (binaryOpPrism eqPrism) (applySub sub conc) of
        Just (l, r) -> decidePolyEq l r
        Nothing     -> Just $ "PolyEq applies only to equalities; got: " ++ show (applySub sub conc)
  where
    conc :: ClassicalSequentOver HOArithSumLex (Form Bool)
    conc = tau `equals` tau'
    eqPrism :: Control.Lens.Prism' (ClassicalSequentOver HOArithSumLex (Term Int -> Term Int -> Form Bool)) ()
    eqPrism = _termEq

------------------------------------------------------------
-- Parser & calculus
------------------------------------------------------------

parseHOArithSumFL :: RuntimeDeductionConfig HOArithSumLex (Form Bool)
                  -> Parsec String u [HOArithSumFL]
parseHOArithSumFL rtc = try parseExtra <|> liftFO
  where
    -- Leibniz's law is renamed "EQ" in this system (parsed in parseExtra);
    -- reject the first-order fragment's "LL" spelling with a pointer.
    liftFO = do rs <- parseFOLogic defaultRuntimeDeductionConfig
                if any (`elem` [LL1, LL2, ALL1, ALL2]) rs
                    then unexpected "rule LL (it is named EQ in this system)"
                    else return (map FO rs)
    parseExtra = do
        r <- choice (map (try . string)
                ["PR", "AS", "Ind", "Poly", "ΣZ", "SumZ", "ΣS", "SumS", "EQ"
                , "Def-U", "Def-I", "Def-C", "Def-P", "Def-S", "Def-=", "Def-\8709", "Def-{}"])
        return $ case r of
            "PR"        -> [Pr (problemPremises rtc)]
            "AS"        -> [As]
            "Ind"       -> [Induction, InductionPlus]
            "Poly"      -> [PolyEq]
            "EQ"        -> map FO [LL1, LL2, ALL1, ALL2]
            "ΣZ"        -> [SumZero]
            "SumZ"      -> [SumZero]
            "ΣS"        -> [SumSucc, SumPlus]
            "SumS"      -> [SumSucc, SumPlus]
            "Def-U"     -> [DefU1, DefU2]
            "Def-I"     -> [DefI1, DefI2]
            "Def-C"     -> [DefC1, DefC2, DefC3, DefC4]
            "Def-S"     -> [DefSub1, DefSub2]
            "Def-P"     -> [DefP1, DefP2]
            "Def-="     -> [DefID1, DefID2, DefID3, DefID4]
            "Def-\8709" -> [DefES1, DefES2, DefES3, DefES4]
            _           -> [DefSep1, DefSep2, DefSep3, DefSep4]

parseHOArithSumFLProof :: RuntimeDeductionConfig HOArithSumLex (Form Bool)
                       -> String
                       -> [DeductionLine HOArithSumFL HOArithSumLex (Form Bool)]
parseHOArithSumFLProof rtc =
    toDeductionFitch (parseHOArithSumFL rtc) hoArithSumParser

hoArithSumFLCalc :: NaturalDeductionCalc HOArithSumFL HOArithSumLex (Form Bool)
hoArithSumFLCalc = mkNDCalc
    { ndRenderer        = FitchStyle StandardFitch
    , ndParseProof      = parseHOArithSumFLProof
    , ndProcessLine     = hoProcessLineFitch
    , ndProcessLineMemo = Just hoProcessLineFitchMemo
    , ndParseForm       = hoArithSumParser
    , ndParseSeq        = parseSeqOver hoArithSumParser
    }
