{-# LANGUAGE UnicodeSyntax, FlexibleInstances #-}
module Text.Regex.Parser () where

import GHC.Exts (IsString(..))

import Text.Parsec.Expr (Assoc(..), Operator(..),
                         buildExpressionParser)
import Text.ParserCombinators.Parsec (Parser, parse, oneOf,
                                      noneOf, choice)
import Text.ParserCombinators.Parsec.Language (emptyDef)
import qualified Text.ParserCombinators.Parsec.Token as T

import Control.Applicative ((<$>))

import Text.Regex.Core

regexLang = emptyDef {
    T.identStart      = T.identLetter regexLang,
    T.identLetter     = noneOf "|*()",
    T.opLetter        = oneOf  "|*",
    T.reservedOpNames = ["|", "*"],
    T.reservedNames   = ["∅", "ε"]
}

lexer = T.makeTokenParser regexLang

char    = T.identLetter regexLang
resOp   = T.reservedOp  lexer
resName = T.reserved    lexer
parens  = T.parens      lexer

regex = buildExpressionParser
        [ [op Postfix "*"   (:*)]
        , [   Infix (return (:⧺)) AssocLeft]
        , [op Infix   "|"   (:+)  AssocLeft]
        ] term where
        term = choice [parens regex, res "∅" Φ,
                       res "ε" Λ, (:#) <$> char]
        op fix name f = fix $ resOp name   >> return f
        res name f    =      resName name >> return f

instance IsString (Regex Char) where
    fromString re = case parse regex "Regex" re of
        Right r    → r
        Left  err  → error $ show err
