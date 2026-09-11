{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.HOArithSum.Parser
    ( hoArithSumParser, hoArithSumMontagueParser, hoArithSumOptions
    , hoArithSumEllipsisParser, ellipsisTerm, isEllipsisTerm
    ) where

import Control.Lens (review, Prism')
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes (UniformlyEq((=*)))
import Carnap.Languages.HOArithSum.Syntax
import Carnap.Languages.Util.LanguageClasses
import Carnap.Languages.Util.GenericParsers
import Carnap.Languages.ClassicalSequent.Parser
import Control.Monad.Identity
import Carnap.Languages.PureFirstOrder.Parser (FirstOrderParserOptions(..), parserFromOptions, parseFreeVar)
import Carnap.Languages.PurePropositional.Parser (standardOpTable)
import Text.Parsec
import Text.Parsec.Expr

extendedSymbols :: [Char]
extendedSymbols = ['_','>','#']

-- | Numerals as syntactic sugar for iterated successors of zero, e.g. '3'
-- for 0'''.
parseNumeral :: (ElementaryArithmeticLanguage lang, Monad m) => ParsecT String u m lang
parseNumeral = do spaces
                  ds <- many1 digit
                  spaces
                  return $ iterate arithSucc arithZero !! read ds

-- | Σ x = 0 .. n . body  (also: Sum x = 0 .. n . body, or Sx = 0 .. n . body).
-- The bound variable must come from the free-variable alphabet so that
-- occurrences in the body parse as the same variable and are correctly
-- captured.  Use one of @stuvwxyz@ for Σ-bound vars in this language.
-- The whole prefix up to the '=' is parsed atomically, so an 'S' that is
-- not followed by a bound variable and '=' (e.g. a predicate 'Sx') fails
-- without consuming input.
sumParser ::
    ( IteratedSumLanguage (FixLang lex (Term Int))
    , BoundVars lex
    , Show (FixLang lex (Term Int))
    , Monad m
    ) => ParsecT String u m (FixLang lex (Term Int))   -- free-variable parser
      -> ParsecT String u m (FixLang lex (Term Int))   -- term parser
      -> ParsecT String u m (FixLang lex (Term Int))
sumParser parseFreeV parseTerm =
        do v <- try $ do _ <- string "Σ" <|> string "S"
                         spaces
                         v <- parseFreeV
                         spaces
                         _ <- char '='
                         return v
           spaces
           _ <- string "0"
           spaces
           _ <- string ".."
           spaces
           n <- parseTerm
           spaces
           _ <- char '.'
           spaces
           body <- parseTerm
           let bf x = subBoundVar v x body
           return $ iteratedSum (show v) n bf

-- | The placeholder term written @...@ in a proof line, standing for the
-- right-hand side of the previous line's equality.  It is a zero-ary string
-- function, so it prints as "..." and is inaccessible to the ordinary
-- function-symbol parser (function names must begin with a lower-case
-- letter).  The ellipsis is resolved after parsing, by the calculus that
-- supports it; see 'Carnap.Languages.HOArithSum.Logic.FosterLaursen'.
ellipsisTerm :: HOArithSumLang (Term Int)
ellipsisTerm = review sf ("...", AZero)
    where sf :: Prism' (HOArithSumLang (Term Int)) (String, Arity (Term Int) (Term Int) (Term Int))
          sf = _stringFunc

isEllipsisTerm :: HOArithSumLang (Term Int) -> Bool
isEllipsisTerm t = t =* ellipsisTerm

parseEllipsis :: Monad m => ParsecT String u m (HOArithSumLang (Term Int))
parseEllipsis = string "..." >> spaces >> return ellipsisTerm

-- | The shared option set, parameterized by whether @...@ is a legal term.
-- It is legal only in proof lines, not in lemma statements or goals.
hoArithSumOptionsWith :: Bool -> FirstOrderParserOptions HOArithSumLex u Identity
hoArithSumOptionsWith allowEllipsis = opts
  where
    opts = FirstOrderParserOptions
        { atomicSentenceParser = \x -> try (equalsParser x)
                                       <|> try (lessThanParser x)
                                       <|> try (inequalityParser x)
                                       <|> parsePredicateString extendedSymbols x
        , quantifiedSentenceParser' = quantifiedSentenceParser
        , freeVarParser = parseFreeVar "stuvwxyz"
        , constantParser = Just (ellipsisParser
                                  <|> parseConstant "abcdefghijklmnopqr"
                                  <|> sumParser vparser tparser)
        , functionParser = Just (\x -> hoArithSumOpParser
                                           (parenParser x
                                            <|> try parseNumeral
                                            <|> try (parseFunctionString extendedSymbols x)
                                            <|> vparser
                                            <|> cparser
                                            ))
        , hasBooleanConstants = True
        , parenRecur = parenOrBracket
        , opTable = standardOpTable
        , finalValidation = const (pure ())
        }
    ellipsisParser | allowEllipsis = try parseEllipsis
                   | otherwise     = parserZero
    cparser = case constantParser opts of Just c -> c
    fparser = case functionParser opts of Just f -> f
    vparser = freeVarParser opts
    tparser = try (fparser tparser) <|> try cparser <|> vparser
    parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

hoArithSumOptions :: FirstOrderParserOptions HOArithSumLex u Identity
hoArithSumOptions = hoArithSumOptionsWith False

hoArithSumParser :: Parsec String u (HOArithSumLang (Form Bool))
hoArithSumParser = parserFromOptions hoArithSumOptions

-- | As 'hoArithSumParser', but additionally accepting @...@ as a term.
hoArithSumEllipsisParser :: Parsec String u (HOArithSumLang (Form Bool))
hoArithSumEllipsisParser = parserFromOptions (hoArithSumOptionsWith True)

hoArithSumMontagueParser :: Parsec String u (HOArithSumLang (Form Bool))
hoArithSumMontagueParser = parserFromOptions hoArithSumOptions { hasBooleanConstants = False }

instance ParsableLex (Form Bool) HOArithSumLex where
    langParser = hoArithSumParser

parseExponentSugar :: Monad m => ParsecT String u m (HOArithSumLang (Term Int) -> HOArithSumLang (Term Int))
parseExponentSugar = do
    _ <- char '^'
    spaces
    ds <- many1 digit
    spaces
    let n = read ds :: Int
    if n < 1 
      then fail "Exponent must be a positive integer"
      else return (\t -> foldr1 arithTimes (replicate n t))

hoArithSumOpParser :: Monad m
    => ParsecT String u m (HOArithSumLang (Term Int))
    -> ParsecT String u m (HOArithSumLang (Term Int))
hoArithSumOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [ Postfix (try (iteratedParse parseSucc))
                      , Postfix (try parseExponentSugar)
                      ]
                    , [Infix (try parseTimes) AssocLeft]
                    , [Infix (try parsePlus) AssocLeft]
                    ]