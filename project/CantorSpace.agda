------------------------------------------------------------------------
-- Project: General Topology
--
-- Cantor space
------------------------------------------------------------------------

module CantorSpace where

open import Agda.Primitive
open import Relation.Binary
open import Data.Bool
open import Data.Nat
open import Data.List
open import Function.Construct.Composition
open import Topology.Core

------------------------------------------------------------------------

infix 4 _⊏_
infix 4 _⊑'_

------------------------------------------------------------------------

-- data ℂ : ℕ → Bool 

data _⊑'_ : Rel (List Bool) lzero where 
    []⊑' : ∀ {l}                            → [] ⊑' l
    ∷⊑'  : ∀ {x l₁ l₂} (l₁⊑'l₂ : l₁ ⊑' l₂) → (x ∷ l₁) ⊑' (x ∷ l₂)

shift : (ℕ → Bool) → (ℕ → Bool)
shift a = λ n → a (suc n)

data _⊏_ : REL (List Bool) (ℕ → Bool) lzero where
    []⊏ : ∀ {a} → [] ⊏ a
    ∷⊏  : ∀ {a l} (l : List Bool) → l ⊏ shift a → a 0 ∷ l ⊏ a
