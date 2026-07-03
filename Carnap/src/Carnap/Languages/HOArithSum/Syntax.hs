{-#LANGUAGE UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, TypeOperators, ScopedTypeVariables, PatternSynonyms, RankNTypes, FlexibleContexts #-}
module Carnap.Languages.HOArithSum.Syntax
where

import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes (Schematizable(schematize))
import Carnap.Core.Data.Util (castTo)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.SetTheory.Syntax
import Carnap.Languages.Arithmetic.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Control.Lens ((^?), preview)

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

-- The generic set-theory 'CopulaSchema' instance can't see the 'BoundedSum'
-- (it lives in the open slot of the lexicon), so it falls back to printing the
-- summand as a raw lambda, e.g. "Σy=0..x. λβ_1.β_-1".  This bespoke instance
-- recognises a bounded sum and prints its body with the bound variable
-- substituted in, e.g. "Σy=0..x. y", the way it was written.  Separation and
-- quantifier bodies are handled exactly as in the generic instance.
instance {-# OVERLAPPING #-} CopulaSchema HOArithSumLang where
    appSchema t@(x :!$: _) (LLam f) e =
        case ( castTo x        :: Maybe (HOArithSumLang (Term Int -> (Term Int -> Term Int) -> Term Int))
             , castTo (LLam f) :: Maybe (HOArithSumLang (Term Int -> Term Int)) ) of
            (Just xb, Just (LLam g)) | Just s <- xb ^? _bsum ->
                schematize t (show (g $ foVar s) : e)
            _ -> case ( castTo x        :: Maybe (HOArithSumLang (Term Int -> (Term Int -> Form Bool) -> Term Int))
                      , castTo (LLam f) :: Maybe (HOArithSumLang (Term Int -> Form Bool)) ) of
                    (Just xs, Just (LLam fs)) | Just s <- xs ^? _separator ->
                        schematize t (show (fs $ foVar s) : e)
                    _ -> schematize t (show (LLam f) : e)
    appSchema h@(Fx _) (LLam f) e =
        case (qtype h >>= preview _all, qtype h >>= preview _some, oftype (LLam f)) of
            (Just x, _, Just (LLam f')) -> schematize (All x) (show (f' $ foVar x) : e)
            (_, Just x, Just (LLam f')) -> schematize (Some x) (show (f' $ foVar x) : e)
            _ -> schematize h (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

-- The same treatment for the sequent-calculus lexicon: lemma statements and
-- proof goals are printed through the 'ClassicalSequentOver' language, whose
-- default instance (the overlappable first-order one) likewise renders bounded
-- sums and separators as raw lambdas.
instance {-# OVERLAPPING #-} CopulaSchema (ClassicalSequentOver HOArithSumLex) where
    appSchema t@(x :!$: _) (LLam f) e =
        case ( castTo x        :: Maybe (ClassicalSequentOver HOArithSumLex (Term Int -> (Term Int -> Term Int) -> Term Int))
             , castTo (LLam f) :: Maybe (ClassicalSequentOver HOArithSumLex (Term Int -> Term Int)) ) of
            (Just xb, Just (LLam g)) | Just s <- xb ^? _bsum ->
                schematize t (show (g $ var s) : e)
            _ -> case ( castTo x        :: Maybe (ClassicalSequentOver HOArithSumLex (Term Int -> (Term Int -> Form Bool) -> Term Int))
                      , castTo (LLam f) :: Maybe (ClassicalSequentOver HOArithSumLex (Term Int -> Form Bool)) ) of
                    (Just xs, Just (LLam fs)) | Just s <- xs ^? _separator ->
                        schematize t (show (fs $ var s) : e)
                    _ -> schematize t (show (LLam f) : e)
    appSchema q@(Fx _) (LLam f) e =
        case ( qtype q >>= preview _all  >>= \x -> (,) <$> Just x <*> castTo (var x :: ClassicalSequentOver HOArithSumLex (Term Int))
             , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (var x :: ClassicalSequentOver HOArithSumLex (Term Int)) ) of
            (Just (x,v), _) -> schematize (All x)  (show (f v) : e)
            (_, Just (x,v)) -> schematize (Some x) (show (f v) : e)
            _ -> schematize q (show (LLam f) : e)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema
