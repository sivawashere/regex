{-# LANGUAGE UnicodeSyntax, RecordWildCards #-}
module Text.Regex.DFA where

import Data.Set (Set)
import Data.Set.Unicode ((∈))

-- | Represents a deterministic finite automaton (DFA)
data DFA q σ = DFA {
    -- | The transition function
    δ  ∷ q → σ → q,
    -- | The initial state
    q₀ ∷ q,
    -- | The set of final states
    f  ∷ Set q
}

-- | Determines whether a DFA accepts an input string
accepts ∷ Ord q ⇒ DFA q σ → [σ] → Bool
DFA{..} `accepts` s = foldl δ q₀ s ∈ f
