module Carnap.Languages.HigherOrderArithmetic.Logic.Gentzen
( openLogicHOArithLKCalc, openLogicHOArithLJCalc )
where

import Carnap.Core.Data.Types
import Carnap.Languages.PureFirstOrder.Logic.OpenLogic
import Carnap.Languages.HigherOrderArithmetic.Parser
import Carnap.Languages.HigherOrderArithmetic.Syntax
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Tableau.Data

openLogicHOArithLKCalc :: TableauCalc UntypedHigherOrderArithLex (Form Bool) OpenLogicFOLK
openLogicHOArithLKCalc = mkTBCalc
    { tbParseForm = untypedHigherOrderArithmeticParser
    , tbParseRule = parseOpenLogicFOLK
    , tbNotation = dropOuterParens
    }

openLogicHOArithLJCalc :: TableauCalc UntypedHigherOrderArithLex (Form Bool) OpenLogicFOLJ
openLogicHOArithLJCalc = mkTBCalc
    { tbParseForm = untypedHigherOrderArithmeticParser
    , tbParseRule = parseOpenLogicFOLJ
    , tbNotation = dropOuterParens
    }
