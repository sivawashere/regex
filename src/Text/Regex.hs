{-# LANGUAGE OverloadedStrings, UnicodeSyntax #-}
module Text.Regex (matches) where

import Prelude.Unicode ((∘))

import Text.Regex.Core
import Text.Regex.DFA (accepts)
import Text.Regex.NFA (toDFA, toNFA, toNFAε)
import Text.Regex.Parser

-- | Synonym for regex strings
type Pattern = Regex Char

 -- | Determines whether an input string matches against a regular expression
matches ∷ String → Pattern → Bool
matches = flip $ accepts ∘ uncurry toDFA ∘ toNFA ∘ toNFAε
