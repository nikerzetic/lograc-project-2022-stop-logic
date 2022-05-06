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

------------------------------------------------------------------------

infix 10 _∩_
infix 9 _∈_
infix 8 _⊆_ 
infix 8 _⊆ᵖ_ 

------------------------------------------------------------------------

-- Powerset
ℙ : {ℓ : Level} → Set ℓ → Set (lsuc lzero ⊔ ℓ)
ℙ A = A → Prop

_∈_ : {ℓ : Level} {A : Set ℓ} → A → ℙ A → Prop
x ∈ S = S x

-- The empty subset
empty : {ℓ : Level} (A : Set ℓ) → ℙ A
empty A  = λ x → ⊥ᵖ

-- The full subset
full : {ℓ : Level} (A : Set ℓ) → ℙ A
full A = λ x → ⊤ᵖ

-- Subset relation
_⊆_ : {ℓ : Level} {A : Set ℓ} → ℙ A → ℙ A → Prop ℓ
S ⊆ T = ∀ x → x ∈ S → x ∈ T

_⊆ᵖ_ : {ℓ : Level} {A : Set ℓ} → ℙ A → ℙ A → Prop
S ⊆ᵖ T = ⟪ S ⊆ T ⟫

-- Equality relation that returns Prop
_≡ᵖ_ : {ℓ : Level} {A : Set ℓ} → ℙ A → ℙ A → Prop
S ≡ᵖ T =  S ⊆ᵖ T ∧ᵖ T ⊆ᵖ S 

-- Subset extensionality
postulate subset-ext : {ℓ : Level} {A : Set ℓ} {S T : ℙ A} → (∀ x → S x ≡ T x) → S ≡ T

⊆-⊇-≡ : {ℓ : Level} {A : Set ℓ} (S T : ℙ A) → S ⊆ T → T ⊆ S → S ≡ T
⊆-⊇-≡ S T S⊆T T⊆S = subset-ext λ x → prop-ext (S⊆T x) (T⊆S x)

-- Union of a family
union : {ℓ k : Level} {I : Set ℓ} {A : Set k} → (I → ℙ A) → ℙ A
union S x = ∃ᵖ (λ i → x ∈ S i)

-- Binary intersection
_∩_ : {ℓ : Level} {A : Set ℓ} → ℙ A → ℙ A → ℙ A
U ∩ V = λ x → U x ∧ᵖ V x

-- Countable set
-- record countable₁ {ℓ} (A : Set ℓ) = Set where 
-- -- ??? Setω₁ 
--     field 
--         ϕ = {!   !}
--         ϕ-injective = {!   !}

-- countable₂ : ?
-- countable₂ A = empty A → ⊤ᵖ
-- countable₂ A = empty A → ⊤ᵖ
