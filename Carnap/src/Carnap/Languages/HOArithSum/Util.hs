{-#LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeOperators #-}
-- | Polynomial-equality decision procedure for HOArithSum terms.
--
-- We decompose a term into the ring 'ℤ[x₁,…,xₖ]', treating any subterm we
-- can't decompose (free variables, schematic vars, Σ-terms, set-typed
-- subterms) as an opaque indeterminate keyed by its canonical 'show'
-- representation.  Two terms are decided polynomial-equal iff their
-- normalized polynomial representations agree.
module Carnap.Languages.HOArithSum.Util
    ( polyNormalize, polyEq, decidePolyEq, Polynomial
    ) where

import Control.Lens (preview)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Carnap.Core.Data.Types
import Carnap.Core.Data.Optics (unaryOpPrism, binaryOpPrism)
import Carnap.Languages.Util.LanguageClasses

type Atom      = String
type Monomial  = [(Atom, Int)]            -- sorted by atom, no zero exponents
type Polynomial = Map Monomial Integer    -- coefficient map; missing key = 0

-- canonicalize a monomial: sort, merge duplicates, drop zero exponents
canonMono :: Monomial -> Monomial
canonMono = filter ((/= 0) . snd) . M.toList . M.fromListWith (+)

mulMono :: Monomial -> Monomial -> Monomial
mulMono a b = canonMono (a ++ b)

polyClean :: Polynomial -> Polynomial
polyClean = M.filter (/= 0)

polyZero :: Polynomial
polyZero = M.empty

polyOne :: Polynomial
polyOne = M.singleton [] 1

polyConst :: Integer -> Polynomial
polyConst 0 = polyZero
polyConst k = M.singleton [] k

polyAtom :: Atom -> Polynomial
polyAtom a = M.singleton [(a, 1)] 1

polyAdd :: Polynomial -> Polynomial -> Polynomial
polyAdd p q = polyClean (M.unionWith (+) p q)

polyMul :: Polynomial -> Polynomial -> Polynomial
polyMul p q = polyClean . M.fromListWith (+) $
    [ (mulMono m1 m2, c1 * c2)
    | (m1, c1) <- M.toList p
    , (m2, c2) <- M.toList q
    ]

-- | Normalize an arithmetic term into a polynomial.
--
-- Recognizes 0, Suc(_), (_+_), (_*_); any other shape becomes a single
-- opaque indeterminate keyed by its 'show'.
polyNormalize ::
    forall lex b. (PrismElementaryArithmeticLex lex b, Show (FixLang lex (Term b)))
    => FixLang lex (Term b) -> Polynomial
polyNormalize t
    | Just ()     <- preview _arithZero t                       = polyZero
    | Just (a, b) <- preview (binaryOpPrism _arithPlus)  t      = polyAdd (polyNormalize a) (polyNormalize b)
    | Just (a, b) <- preview (binaryOpPrism _arithTimes) t      = polyMul (polyNormalize a) (polyNormalize b)
    | Just a      <- preview (unaryOpPrism  _arithSucc)  t      = polyAdd (polyNormalize a) polyOne
    | otherwise                                                 = polyAtom (show t)

polyEq :: Polynomial -> Polynomial -> Bool
polyEq p q = polyClean p == polyClean q

-- | Returns 'Nothing' if the two terms are polynomial-equal under the
-- 'opaque indeterminate' interpretation; otherwise an error string.
decidePolyEq ::
    (PrismElementaryArithmeticLex lex b, Show (FixLang lex (Term b)))
    => FixLang lex (Term b) -> FixLang lex (Term b) -> Maybe String
decidePolyEq lhs rhs
    | polyEq (polyNormalize lhs) (polyNormalize rhs) = Nothing
    | otherwise = Just $ "the equation " ++ show lhs ++ " = " ++ show rhs
                         ++ " is not a polynomial identity"
