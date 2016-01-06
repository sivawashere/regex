module Text.Regex.Core where

-- | The Regex ADT
data Regex σ
             -- | ∅
             = Φ
             -- | ε
             | Λ
             -- | Literal
             | (:#) σ
             -- | Concatenation
             | (Regex σ) :⧺ (Regex σ)
             -- | Alternation
             | (Regex σ) :+ (Regex σ)
             -- | Kleene star
             | (:*) (Regex σ)
