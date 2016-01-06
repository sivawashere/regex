{-# LANGUAGE UnicodeSyntax, RecordWildCards, LambdaCase #-}
module Text.Regex.NFA where

import Prelude hiding (map, null, filter)
import qualified Prelude as P
import Prelude.Unicode (ℤ, (≡), (∨), (∧), (∘))
import Data.Ord.Unicode ((≤), (≥))

import Data.Set (Set, fromList, toList, toAscList,
                 singleton, unions, map, null, filter,
                 findMin, findMax, insert, delete)
import Data.Set.Unicode ((∅), (∋), (∩), (∪), (∖))

import Control.Monad (foldM)

import Data.List (subsequences)

import Text.Regex.Core
import Text.Regex.DFA (DFA(..))

-- | Represents a nondeterministic finite automaton (NFA)
data NFA q σ = NFA {
    -- | The transition function
    δ  ∷ q → σ → Set q,
    -- | The initial state
    q₀ ∷ q,
    -- | The set of final states
    f  ∷ Set q
}

-- | Represents NFA-ε
type NFAε q σ = NFA q (Maybe σ)

-- | A special NFA that keeps track of all of its states
type RNFA q σ = (Set q, NFA q σ)

-- | Analogous to the RNFA, but for NFA-ε
type RNFAε q σ = (Set q, NFAε q σ)

-- | Determines whether an NFA accepts an input string
accepts ∷ Ord q ⇒ NFA q σ → [σ] → Bool
accepts NFA{..} = any ((∋)f) ∘ foldM ((toList ∘) ∘ δ) q₀

-- | Converts a regex to an NFA-ε that obeys the following invariants
--      * Generated automata have exactly one final state
--      * Final states are not co-accessible from other states
--      * States are dense and ordered
toNFAε ∷ Eq σ ⇒ Regex σ → RNFAε ℤ σ
toNFAε = let zero = singleton 0
             one  = singleton 1
             bin  = fromList [0, 1]
             hd   = head ∘ toList in \case
                                           
    Φ        → (zero, NFA (\_ _ → (∅)) 0 (∅))
    
    Λ        → (bin, NFA δ 0 one) where
        δ 0 Nothing = one
        δ _ _       = (∅)
    
    (:#) a   → (bin, NFA δ 0 one) where
        δ 0 (Just c) = if c ≡ a then one else (∅)
        δ _ _        = (∅)
    
    r₁ :⧺ r₂ → (q', NFA δ' q₀₁ $ singleton f₂') where
        (q₁, NFA {q₀ = q₀₁, δ = δ₁, f = f₁}) = toNFAε r₁
        (q₂, NFA {q₀ = q₀₂, δ = δ₂, f = f₂}) = toNFAε r₂
        
        update = (findMax q₁) - (findMin q₂)
        
        (f₁', f₂') = (hd f₁, hd f₂ + update)
        q₂'        = map (+ update) $ delete q₀₂ q₂
        q'         = q₁ ∪ q₂'
        
        δ' q s | q ≥ q₀₁ ∧ q < f₁' = δ₁ q s
               | q ≥ f₁' ∧ q ≤ f₂' = map (+ update) $ δ₂ (q - update) s
               | otherwise         = (∅)
        
    r₁ :+ r₂ → (q', NFA δ' q₀' f') where
        (q₁, NFA {q₀ = q₀₁, δ = δ₁, f = f₁}) = toNFAε r₁
        (q₂, NFA {q₀ = q₀₂, δ = δ₂, f = f₂}) = toNFAε r₂
        
        update = (findMax q₁) - (findMin q₂) + 1
        
        q₂'        = map (+ update) q₂
        (f₁', f₂') = (hd f₁, hd f₂ + update)
        (q₀', f')  = (q₀₁ - 1, singleton $ f₂' + 1)
        q₀₂'       = q₀₂ + update
        q'         = insert q₀' $ q₁ ∪ q₂' ∪ f'
        
        δ' q s |  q ≡ q₀'             ∧ s ≡ Nothing = fromList [q₀₁, q₀₂']
               | (q ≡ f₁'  ∨ q ≡ f₂') ∧ s ≡ Nothing = f'
               |  q ≥ q₀₁  ∧ q ≤ f₁'                = δ₁ q s
               |  q ≥ q₀₂' ∧ q ≤ f₂'                = map (+ update) $ δ₂ (q - update) s
               | otherwise                          = (∅)
               
    (:*) r → (q', NFA δ' q₀' f') where
        (q, NFA{..})  = toNFAε r
        (q₀', f₀)     = (findMin q - 1, hd f)
        f'            = singleton $ findMax q + 1
        q'            = insert q₀' $ q ∪ f'
        
        δ' q s | (q ≡ q₀' ∨ q ≡ f₀) ∧ s ≡ Nothing = singleton q₀ ∪ f'
               | otherwise                        = δ q s

-- | Converts an NFA-ε to a regular NFA
toNFA ∷ Ord q ⇒ RNFAε q σ → RNFA q σ
toNFA (q, NFA{..}) = (q, NFA δ' q₀ f') where
    δ' q' s = unions $ toList $ map (flip δ $ Just s) $ εs $ singleton q'
    f'      = filter (not ∘ null ∘ (∩) f ∘ εs ∘ singleton) q
    
    εs = transCl (flip δ $ Nothing)
    transCl f set | null diff = set
                  | otherwise = transCl f $ set ∪ diff
        where diff = (unions $ toList $ map f set) ∖ set

-- | Converts an NFA to a DFA
toDFA ∷ Ord q ⇒ Set q → NFA q σ → DFA (Set q) σ
toDFA q NFA{..} = DFA δ' (singleton q₀) f' where
    δ' q'' s = unions $ toList $ map (flip δ s) q''
    q'       = fromList $ P.map fromList $ subsequences $ toAscList q
    f'       = filter (not ∘ null ∘ (∩) f) q'
