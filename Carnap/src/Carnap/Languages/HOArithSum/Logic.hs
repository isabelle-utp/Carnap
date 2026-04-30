{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.Languages.HOArithSum.Logic
    ( ofHOArithSumSys
    , module Carnap.Languages.HOArithSum.Logic.FosterLaursen
    ) where

import Carnap.Core.Data.Types
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Languages.Util.LanguageClasses (Incrementable)
import Carnap.Languages.HOArithSum.Syntax
import Carnap.Languages.HOArithSum.Logic.FosterLaursen

ofHOArithSumSys :: (forall r .
                    ( SupportsND r HOArithSumLex (Form Bool)
                    , Incrementable HOArithSumLex (Term Int)
                ) => NaturalDeductionCalc r HOArithSumLex (Form Bool) -> a) -> String -> Maybe a
ofHOArithSumSys f sys
    | sys == "hoArithSumFL" = Just $ f hoArithSumFLCalc
    | otherwise             = Nothing
