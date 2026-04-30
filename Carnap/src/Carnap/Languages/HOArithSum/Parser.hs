{-#LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.HOArithSum.Parser
    ( hoArithSumParser, hoArithSumMontagueParser, hoArithSumOptions
    ) where

import Carnap.Core.Data.Types
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

-- | '1' as syntactic sugar for Suc(0)
parseOne :: (ElementaryArithmeticLanguage lang, Monad m) => ParsecT String u m lang
parseOne = try $ spaces >> string "1" >> spaces >> return (arithSucc arithZero)

-- | Σ x = 0 .. n . body  (also: Sum x = 0 .. n . body).
-- The bound variable must come from the free-variable alphabet so that
-- occurrences in the body parse as the same variable and are correctly
-- captured.  Use one of @stuvwxyz@ for Σ-bound vars in this language.
sumParser ::
    ( IteratedSumLanguage (FixLang lex (Term Int))
    , BoundVars lex
    , Show (FixLang lex (Term Int))
    , Monad m
    ) => ParsecT String u m (FixLang lex (Term Int))   -- free-variable parser
      -> ParsecT String u m (FixLang lex (Term Int))   -- term parser
      -> ParsecT String u m (FixLang lex (Term Int))
sumParser parseFreeV parseTerm =
        do _ <- try (string "Σ") <|> try (string "Sum ") <|> try (string "sum ")
           spaces
           v <- parseFreeV
           spaces
           _ <- char '='
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

hoArithSumOptions :: FirstOrderParserOptions HOArithSumLex u Identity
hoArithSumOptions = FirstOrderParserOptions
    { atomicSentenceParser = \x -> try (elementParser x)
                                   <|> try (equalsParser x)
                                   <|> try (lessThanParser x)
                                   <|> try (inequalityParser x)
                                   <|> subsetParser x
                                   <|> parsePredicateString extendedSymbols x
    , quantifiedSentenceParser' = quantifiedSentenceParser
    , freeVarParser = parseFreeVar "stuvwxyz"
    , constantParser = Just (parseConstant "abcdefghijklmnopqr"
                              <|> try parseEmptySet
                              <|> try (separationParser vparser tparser
                                          (parserFromOptions hoArithSumOptions))
                              <|> sumParser vparser tparser)
    , functionParser = Just (\x -> hoArithSumOpParser
                                       (parenParser x
                                        <|> powersetParser x
                                        <|> try parseOne
                                        <|> parseZero
                                        <|> try parseEmptySet
                                        <|> try (parseFunctionString extendedSymbols x)
                                        <|> vparser
                                        <|> cparser
                                        ))
    , hasBooleanConstants = True
    , parenRecur = parenOrBracket
    , opTable = standardOpTable
    , finalValidation = const (pure ())
    }
    where cparser = case constantParser hoArithSumOptions of Just c -> c
          fparser = case functionParser hoArithSumOptions of Just f -> f
          vparser = freeVarParser hoArithSumOptions
          tparser = try (fparser tparser) <|> try cparser <|> vparser
          parenOrBracket opt rw = (wrappedWith '(' ')' (rw opt) <|> wrappedWith '[' ']' (rw opt))

hoArithSumParser :: Parsec String u (HOArithSumLang (Form Bool))
hoArithSumParser = parserFromOptions hoArithSumOptions

hoArithSumMontagueParser :: Parsec String u (HOArithSumLang (Form Bool))
hoArithSumMontagueParser = parserFromOptions hoArithSumOptions { hasBooleanConstants = False }

instance ParsableLex (Form Bool) HOArithSumLex where
    langParser = hoArithSumParser

hoArithSumOpParser :: Monad m
    => ParsecT String u m (HOArithSumLang (Term Int))
    -> ParsecT String u m (HOArithSumLang (Term Int))
hoArithSumOpParser subTerm = buildExpressionParser opTable subTerm
    where opTable = [ [Postfix (try (iteratedParse parseSucc))]
                    , [Infix (try parsePlus) AssocLeft, Infix (try parseTimes) AssocLeft]
                    , [Infix (try parseIntersect) AssocLeft, Infix (try parseUnion) AssocLeft]
                    , [Infix (try parseComplement) AssocNone]
                    ]
