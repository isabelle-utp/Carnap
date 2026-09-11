{-#LANGUAGE TypeSynonymInstances, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, GADTs, DataKinds, PolyKinds, TypeOperators, ViewPatterns, PatternSynonyms, RankNTypes, FlexibleContexts, ScopedTypeVariables #-}
module Carnap.Languages.HOArithSum.Syntax
where

import Control.Lens
import Data.Typeable
import Data.Char (isDigit)
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics
import Carnap.Core.Data.Classes (Schematizable(schematize))
import Carnap.Core.Data.Util (castTo)
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.PureFirstOrder.Syntax
import Carnap.Languages.Util.GenericConstructors
import Carnap.Languages.Arithmetic.Syntax
import Carnap.Languages.ClassicalSequent.Syntax

type HOArithSumLex = OpenLexiconArith
        ( Predicate ArithStringPred :|: Function ArithStringFunc :|: BoundedSum Int )

type HOArithSumLang = FixLang HOArithSumLex

instance PrismBoundedSum HOArithSumLex Int
instance PrismPolyadicStringPredicate HOArithSumLex Int Bool
instance PrismPolyadicStringFunction HOArithSumLex Int Int

instance Incrementable HOArithSumLex (Term Int) where
    incHead = const Nothing
        & outside (_stringPred') .~ (\(s,a) -> Just $ stringPred s (ASucc a))
        & outside (_spredIdx')   .~ (\(n,a) -> Just $ pphin n (ASucc a))
        & outside (_stringFunc') .~ (\(s,a) -> Just $ stringFunc s (ASucc a))
        & outside (_sfuncIdx')   .~ (\(n,a) -> Just $ spfn n (ASucc a))
        & outside (_funcIdx')    .~ (\(n,a) -> Just $ pfn n (ASucc a))
        where _stringPred' :: Typeable ret => Prism' (HOArithSumLang ret) (String, Arity (Term Int) (Form Bool) ret)
              _stringPred' = _stringPred
              _spredIdx' :: Typeable ret => Prism' (HOArithSumLang ret) (Int, Arity (Term Int) (Form Bool) ret)
              _spredIdx' = _spredIdx
              _funcIdx' :: Typeable ret => Prism' (HOArithSumLang ret) (Int, Arity (Term Int) (Term Int) ret)
              _funcIdx' = _funcIdx
              _sfuncIdx' :: Typeable ret => Prism' (HOArithSumLang ret) (Int, Arity (Term Int) (Term Int) ret)
              _sfuncIdx' = _sfuncIdx
              _stringFunc' :: Typeable ret => Prism' (HOArithSumLang ret) (String, Arity (Term Int) (Term Int) ret)
              _stringFunc' = _stringFunc

instance (Sequentable lex, PrismBoundedSum lex b)
        => PrismBoundedSum (ClassicalSequentLexOver lex) b where
        link_bsum = underlyingLex . link_bsum . relexIso

instance (Sequentable lex, PrismElementaryArithmeticLex lex b)
        => PrismElementaryArithmeticLex (ClassicalSequentLexOver lex) b where
        unarylink_ArithmeticLex  = underlyingLex . unarylink_ArithmeticLex  . relexIso
        binarylink_ArithmeticLex = underlyingLex . binarylink_ArithmeticLex . relexIso
        zeroarylink_ArithmeticLex = underlyingLex . zeroarylink_ArithmeticLex . relexIso

-- The generic first-order 'CopulaSchema' instance can't see the 'BoundedSum'
-- (it lives in the open slot of the lexicon), so it falls back to printing the
-- summand as a raw lambda, e.g. "Σy=0..x. λβ_1.β_-1".  This bespoke instance
-- recognises a bounded sum and prints its body with the bound variable
-- substituted in, e.g. "Σy=0..x. y", the way it was written.  Quantifier
-- bodies are handled exactly as in the generic instance.
--
-- It also prints concrete numbers as numerals: since printing is bottom-up
-- over strings and zero prints as "0", a successor whose argument printed as
-- a numeral prints as the next numeral, so 0''' renders as "3".
instance {-# OVERLAPPING #-} CopulaSchema HOArithSumLang where
    appSchema t@(x :!$: _) (LLam f) e =
        case ( castTo x        :: Maybe (HOArithSumLang (Term Int -> (Term Int -> Term Int) -> Term Int))
             , castTo (LLam f) :: Maybe (HOArithSumLang (Term Int -> Term Int)) ) of
            (Just xb, Just (LLam g)) | Just s <- xb ^? _bsum ->
                schematize t (show (g $ foVar s) : e)
            _ -> schematize t (show (LLam f) : e)
    appSchema h@(Fx _) (LLam f) e =
        case (qtype h >>= preview _all, qtype h >>= preview _some, oftype (LLam f)) of
            (Just x, _, Just (LLam f')) -> schematize (All x) (show (f' $ foVar x) : e)
            (_, Just x, Just (LLam f')) -> schematize (Some x) (show (f' $ foVar x) : e)
            _ -> schematize h (show (LLam f) : e)
    appSchema x@(Fx _) y@(Fx _) e
        | Just s <- castTo x :: Maybe (HOArithSumLang (Term Int -> Term Int))
        , Just () <- s ^? _arithSucc
        , let shown = show y
        , all isDigit shown
        = show (read shown + 1 :: Integer)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema

-- The same treatment for the sequent-calculus lexicon: lemma statements and
-- proof goals are printed through the 'ClassicalSequentOver' language, whose
-- default instance (the overlappable first-order one) likewise renders bounded
-- sums as raw lambdas.  Concrete numbers are again rendered as numerals.
instance {-# OVERLAPPING #-} CopulaSchema (ClassicalSequentOver HOArithSumLex) where
    appSchema t@(x :!$: _) (LLam f) e =
        case ( castTo x        :: Maybe (ClassicalSequentOver HOArithSumLex (Term Int -> (Term Int -> Term Int) -> Term Int))
             , castTo (LLam f) :: Maybe (ClassicalSequentOver HOArithSumLex (Term Int -> Term Int)) ) of
            (Just xb, Just (LLam g)) | Just s <- xb ^? _bsum ->
                schematize t (show (g $ var s) : e)
            _ -> schematize t (show (LLam f) : e)
    appSchema q@(Fx _) (LLam f) e =
        case ( qtype q >>= preview _all  >>= \x -> (,) <$> Just x <*> castTo (var x :: ClassicalSequentOver HOArithSumLex (Term Int))
             , qtype q >>= preview _some >>= \x -> (,) <$> Just x <*> castTo (var x :: ClassicalSequentOver HOArithSumLex (Term Int)) ) of
            (Just (x,v), _) -> schematize (All x)  (show (f v) : e)
            (_, Just (x,v)) -> schematize (Some x) (show (f v) : e)
            _ -> schematize q (show (LLam f) : e)
    appSchema x@(Fx _) y@(Fx _) e
        | Just s <- castTo x :: Maybe (ClassicalSequentOver HOArithSumLex (Term Int -> Term Int))
        , Just () <- s ^? _arithSucc
        , let shown = show y
        , all isDigit shown
        = show (read shown + 1 :: Integer)
    appSchema x y e = schematize x (show y : e)

    lamSchema = defaultLamSchema
