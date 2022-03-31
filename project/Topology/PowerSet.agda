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
Pset : {ℓ : Level} → Set ℓ → Set (lsuc lzero ⊔ ℓ)
Pset A = A → Prop

-- McP v VS Code ne deluje pravilno (razume ga kot dva znaka). 
-- Alternative za potencno mnozico: Γ ß § ℙ ¶ Pset (Gamma ss S P)

infix 3 _∈_
_∈_ : {ℓ : Level} {A : Set ℓ} → A → Pset A → Prop
x ∈ S = S x

-- The empty subset
empty : {ℓ : Level} (X : Set ℓ) → Pset X
empty _ _ = ⊥ᵖ

-- The full subset
full : {ℓ : Level} (X : Set ℓ) → Pset X
full _ _ = ⊤ᵖ

-- Subset relation
_⊆_ : {ℓ : Level} {A : Set ℓ} → Pset A → Pset A → Prop ℓ
S ⊆ T = ∀ x → x ∈ S → x ∈ T

-- Subset extensionality
postulate subset-ext : {ℓ : Level} {A : Set ℓ} {S T : Pset A} → (∀ x → S x ≡ T x) → S ≡ T

⊆-⊇-≡ : {ℓ : Level} {A : Set ℓ} (S T : Pset A) → S ⊆ T → T ⊆ S → S ≡ T
⊆-⊇-≡ S T S⊆T T⊆S = subset-ext λ x → prop-ext (S⊆T x) (T⊆S x)

-- Union of a family
union : {ℓ k : Level} {I : Set ℓ} {A : Set k} → (I → Pset A) → Pset A
union S x = ∃ᵖ (λ i → x ∈ S i)

-- Binary intersection
_∩_ : {ℓ : Level} {A : Set ℓ} → Pset A → Pset A → Pset A
U ∩ V = λ x → U x ∧ᵖ V x