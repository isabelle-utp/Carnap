{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.HigherOrderArithmetic.Logic where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics (ReLex)
import Carnap.Calculi.Tableau.Data
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.HigherOrderArithmetic.Syntax
import Carnap.Languages.HigherOrderArithmetic.Logic.OpenLogic
import Carnap.Languages.HigherOrderArithmetic.Logic.Gentzen
import Carnap.Languages.HigherOrderArithmetic.Logic.Carnap
import Carnap.Languages.Util.LanguageClasses

ofHigherOrderArithmeticTreeSys :: (forall r . 
                    ( Show r
                    , SupportsND r UntypedHigherOrderArithLex (Form Bool)
                    , StructuralInference r UntypedHigherOrderArithLex (ProofTree r UntypedHigherOrderArithLex (Form Bool))
                    , StructuralOverride r (ProofTree r UntypedHigherOrderArithLex (Form Bool))
                ) => TableauCalc UntypedHigherOrderArithLex (Form Bool) r -> a) -> String -> Maybe a
ofHigherOrderArithmeticTreeSys f sys | sys == "openLogicExHOArithNK"    = Just $ f openLogicArithExHOArithNKCalc
                                     | otherwise                        = Nothing

ofHigherOrderArithmeticSeqSys :: (forall r .
                    ( Show r
                    , CoreInference r UntypedHigherOrderArithLex (Form Bool)
                    , SpecifiedUnificationType r
                ) => TableauCalc UntypedHigherOrderArithLex (Form Bool) r -> a) -> String -> Maybe a
ofHigherOrderArithmeticSeqSys f sys | sys == "openLogicExHOArithLK"  = Just $ f openLogicHOArithLKCalc
                                    | sys == "openLogicExHOArithLJ"  = Just $ f openLogicHOArithLJCalc
                                    | otherwise                      = Nothing

ofHigherOrderArithmeticSys :: (forall r .
                    ( SupportsND r UntypedHigherOrderArithLex (Form Bool)
                    , Incrementable UntypedHigherOrderArithLex (Term Int)
                ) => NaturalDeductionCalc r UntypedHigherOrderArithLex (Form Bool) -> a) -> String -> Maybe a
ofHigherOrderArithmeticSys f sys | sys == "openLogicExHOArith" = Just $ f hoArithCalc
                                  | otherwise                  = Nothing
