------------------------------------------------------------------------
-- Project ???
--
-- Subsets and power sets
------------------------------------------------------------------------

{-# OPTIONS --prop #-}

module Topology.PowerSet where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Topology.Logic

-- Powerset
PSet : {ℓ : Level} → Set ℓ → Set (lsuc lzero ⊔ ℓ)
PSet A = A → Prop

-- McP v VS Code ne deluje pravilno (razume ga kot dva znaka). 
-- Alternative za potencno mnozico: Γ ß § ℙ ¶ PSet (Gamma ss S P)

infix 3 _∈_
_∈_ : {ℓ : Level} {A : Set ℓ} → A → PSet A → Prop
x ∈ S = S x

-- The empty subset
empty : {ℓ : Level} (X : Set ℓ) → PSet X
empty _ _ = ⊥ᵖ

-- The full subset
full : {ℓ : Level} (X : Set ℓ) → PSet X
full _ _ = ⊤ᵖ

-- Subset relation
_⊆_ : {ℓ : Level} {A : Set ℓ} → PSet A → PSet A → Prop ℓ
S ⊆ T = ∀ x → x ∈ S → x ∈ T

-- Subset extensionality
postulate subset-ext : {ℓ : Level} {A : Set ℓ} {S T : PSet A} → (∀ x → S x ≡ T x) → S ≡ T

⊆-⊇-≡ : {ℓ : Level} {A : Set ℓ} (S T : PSet A) → S ⊆ T → T ⊆ S → S ≡ T
⊆-⊇-≡ S T S⊆T T⊆S = subset-ext λ x → prop-ext (S⊆T x) (T⊆S x)

-- Union of a family
union : {ℓ k : Level} {I : Set ℓ} {A : Set k} → (I → PSet A) → PSet A
union S x = ∃ᵖ (λ i → x ∈ S i)

-- Binary intersection
_∩_ : {ℓ : Level} {A : Set ℓ} → PSet A → PSet A → PSet A
U ∩ V = λ x → U x ∧ᵖ V x