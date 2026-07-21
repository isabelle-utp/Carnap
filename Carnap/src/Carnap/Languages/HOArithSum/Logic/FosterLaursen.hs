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
import Carnap.Languages.PureFirstOrder.Logic.Rules
import qualified Carnap.Languages.PurePropositional.Logic.FosterAndLaursen as P
import Carnap.Languages.PurePropositional.Logic.Rules (axiom, premConstraint, fitchAssumptionCheck)
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

-- The rule set follows the FosterAndLaursen naming scheme: the full TFL
-- layer (including derived rules) is embedded via the 'TFL' wrapper, and
-- the quantifier and identity rules mirror FosterAndLaursenFOL.  On top of
-- that sit the arithmetic rules particular to this system.
data HOArithSumFL
    = TFL P.FosterAndLaursenTFL
    -- quantifier rules
    | UI | UE | EI | EE1 | EE2
    -- identity rules
    | IDI | IDE1 | IDE2
    -- quantifier negation
    | QN1 | QN2 | QN3 | QN4
    -- arithmetic / sum rules
    | Induction | InductionPlus
    | PolyEq
    | SumZero
    | SumSucc | SumPlus
    -- premise
    | Pr (Maybe [(ClassicalSequentOver HOArithSumLex (Sequent (Form Bool)))])
    deriving Eq

instance Show HOArithSumFL where
    show (TFL x)   = show x
    show UI        = "∀I"
    show UE        = "∀E"
    show EI        = "∃I"
    show EE1       = "∃E"; show EE2 = "∃E"
    show IDI       = "=I"
    show IDE1      = "=E"; show IDE2 = "=E"
    show QN1       = "CQ"; show QN2 = "CQ"
    show QN3       = "CQ"; show QN4 = "CQ"
    show Induction = "Ind"; show InductionPlus = "Ind"
    show PolyEq    = "Poly"
    show SumZero   = "ΣZ"
    show SumSucc   = "ΣS"; show SumPlus = "ΣS"
    show (Pr _)    = "PR"

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
    ruleOf r@(TFL _) = premisesOf r ∴ conclusionOf r
    ruleOf (Pr _)    = axiom
    ruleOf UI        = universalGeneralization
    ruleOf UE        = universalInstantiation
    ruleOf EI        = existentialGeneralization
    ruleOf EE1       = existentialDerivation !! 0
    ruleOf EE2       = existentialDerivation !! 1
    ruleOf IDI       = eqReflexivity
    ruleOf IDE1      = leibnizLawVariations !! 0
    ruleOf IDE2      = leibnizLawVariations !! 1
    ruleOf QN1       = quantifierNegation !! 0
    ruleOf QN2       = quantifierNegation !! 1
    ruleOf QN3       = quantifierNegation !! 2
    ruleOf QN4       = quantifierNegation !! 3
    ruleOf Induction = inductionRule
    ruleOf InductionPlus = inductionPlusRule
    ruleOf PolyEq    = polyEqRule
    ruleOf SumZero   = sumZeroRule
    ruleOf SumSucc   = sumSuccRule
    ruleOf SumPlus   = sumPlusRule

    premisesOf (TFL x) = map liftSequent (premisesOf x)
    premisesOf r = upperSequents (ruleOf r)

    conclusionOf (TFL x) = liftSequent (conclusionOf x)
    conclusionOf r = lowerSequent (ruleOf r)

    indirectInference (TFL x) = indirectInference x
    indirectInference Induction     = Just assumptiveProof
    indirectInference InductionPlus = Just assumptiveProof
    indirectInference x
        | x `elem` [EE1, EE2] = Just assumptiveProof
        | otherwise = Nothing

    restriction (Pr prems)  = Just (premConstraint prems)
    restriction UI          = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1))
        where stau = liftToSequent tau
    restriction EE1         = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction EE2         = Just (eigenConstraint stau (SS (lsome "v" $ phi' 1) :-: SS (phin 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction Induction   = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction InductionPlus = Just (eigenConstraint stau (SS (lall "v" $ phi' 1)) (fogamma 1 :+: fogamma 2))
        where stau = liftToSequent tau
    restriction PolyEq      = Just polyEqConstraint
    restriction _           = Nothing

    globalRestriction (Left ded) n (TFL (P.Core P.CondIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
    globalRestriction (Left ded) n (TFL (P.Core P.CondIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2])]
    globalRestriction (Left ded) n (TFL (P.Core P.BicoIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
    globalRestriction (Left ded) n (TFL (P.Core P.BicoIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
    globalRestriction (Left ded) n (TFL (P.Core P.BicoIntro3)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
    globalRestriction (Left ded) n (TFL (P.Core P.BicoIntro4)) = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 2]), ([phin 2], [phin 1])]
    globalRestriction (Left ded) n (TFL (P.Core P.DisjElim1))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
    globalRestriction (Left ded) n (TFL (P.Core P.DisjElim2))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
    globalRestriction (Left ded) n (TFL (P.Core P.DisjElim3))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
    globalRestriction (Left ded) n (TFL (P.Core P.DisjElim4))  = Just $ fitchAssumptionCheck n ded [([phin 1], [phin 3]), ([phin 2], [phin 3])]
    globalRestriction (Left ded) n (TFL (P.Core P.NegeIntro1)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
    globalRestriction (Left ded) n (TFL (P.Core P.NegeIntro2)) = Just $ fitchAssumptionCheck n ded [([phin 1], [lfalsum])]
    globalRestriction (Left ded) n (TFL (P.Core P.Indirect1))  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
    globalRestriction (Left ded) n (TFL (P.Core P.Indirect2))  = Just $ fitchAssumptionCheck n ded [([lneg $ phin 1], [lfalsum])]
    globalRestriction (Left ded) n UI =
        Just (notAssumedConstraint n ded (taun 1 :: ClassicalSequentOver HOArithSumLex (Term Int)))
    globalRestriction (Left ded) n r | r `elem` [EE1, EE2] =
        case dependencies (ded !! (n - 1)) of
            Just ls -> firstDistinct ls
            Nothing -> Nothing
        where firstDistinct [] = Nothing
              firstDistinct ((a,b):xs) | a /= b = Just (notAssumedConstraint a ded (taun 1 :: ClassicalSequentOver HOArithSumLex (Term Int)))
                                       | otherwise = firstDistinct xs
    -- Fitch-style scope: induction's second premise is a subproof.
    globalRestriction (Left ded) n Induction =
        Just (notAssumedConstraint n ded (taun 1 :: ClassicalSequentOver HOArithSumLex (Term Int)))
    globalRestriction (Left ded) n InductionPlus =
        Just (notAssumedConstraint n ded (taun 1 :: ClassicalSequentOver HOArithSumLex (Term Int)))
    globalRestriction _ _ _ = Nothing

    isAssumption (TFL x) = isAssumption x
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
parseHOArithSumFL rtc =
        try parseArith <|> try premRule <|> try liftProp <|> try quantRule <|> eqReject
  where
    -- The propositional layer is parsed with the default config so that its
    -- "PR" can't fire with propositional premises; ours is tried first.
    liftProp = map TFL <$> P.parseFosterAndLaursenTFL defaultRuntimeDeductionConfig
    premRule = string "PR" >> return [Pr (problemPremises rtc)]
    -- Leibniz's law was called "EQ" in an earlier version of this system;
    -- reject that spelling with a pointer to the current name.
    eqReject = string "EQ" >> unexpected "rule EQ (it is named =E in this system)"
    parseArith = do
        r <- choice (map (try . string) ["Ind", "Poly", "ΣZ", "SumZ", "ΣS", "SumS"])
        return $ case r of
            "Ind"  -> [Induction, InductionPlus]
            "Poly" -> [PolyEq]
            r | r `elem` ["ΣZ", "SumZ"] -> [SumZero]
              | otherwise               -> [SumSucc, SumPlus]
    quantRule = do
        r <- choice (map (try . string) [ "∀I", "@I", "AI", "∀E", "@E", "AE"
                                        , "∃I", "3I", "EI", "∃E", "3E", "EE"
                                        , "=I", "=E", "CQ"])
        return $ case r of
            r | r `elem` ["∀I","@I","AI"] -> [UI]
              | r `elem` ["∀E","@E","AE"] -> [UE]
              | r `elem` ["∃I","3I","EI"] -> [EI]
              | r `elem` ["∃E","3E","EE"] -> [EE1, EE2]
              | r == "=I" -> [IDI]
              | r == "=E" -> [IDE1, IDE2]
              | otherwise -> [QN1, QN2, QN3, QN4]

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
