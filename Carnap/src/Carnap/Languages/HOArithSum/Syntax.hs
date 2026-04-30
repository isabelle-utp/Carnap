{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, TypeOperators, ScopedTypeVariables, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.HOArithSum.Syntax
where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.Arithmetic.Syntax
import Carnap.Languages.ClassicalSequent.Syntax

type HOArithSumLex = ExtendedSeparativeSetTheoryLexOpen
        ( Predicate ArithLessThan :|: Function ArithOps :|: BoundedSum Int )

type HOArithSumLang = FixLang HOArithSumLex

instance PrismTermLessThan HOArithSumLex Int Bool
instance PrismElementaryArithmeticLex HOArithSumLex Int
instance PrismBoundedSum HOArithSumLex Int

instance (Sequentable lex, PrismBoundedSum lex b)
        => PrismBoundedSum (ClassicalSequentLexOver lex) b where
        link_bsum = underlyingLex . link_bsum . relexIso

instance (Sequentable lex, PrismElementaryArithmeticLex lex b)
        => PrismElementaryArithmeticLex (ClassicalSequentLexOver lex) b where
        unarylink_ArithmeticLex  = underlyingLex . unarylink_ArithmeticLex  . relexIso
        binarylink_ArithmeticLex = underlyingLex . binarylink_ArithmeticLex . relexIso
        zeroarylink_ArithmeticLex = underlyingLex . zeroarylink_ArithmeticLex . relexIso
