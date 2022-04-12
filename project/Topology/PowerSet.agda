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

infix 4 _∩_
infix 3 _∈_
infix 3 _⊆_ 

------------------------------------------------------------------------

-- Powerset
ℙ : {ℓ : Level} → Set ℓ → Set (lsuc lzero ⊔ ℓ)
ℙ A = A → Prop

_∈_ : {ℓ : Level} {A : Set ℓ} → A → ℙ A → Prop
x ∈ S = S x

-- The empty subset
empty : {ℓ : Level} (A : Set ℓ) → ℙ A
empty _ = λ _ → ⊥ᵖ

-- The full subset
full : {ℓ : Level} (A : Set ℓ) → ℙ A
full _ = λ _ → ⊤ᵖ

-- Subset relation
_⊆_ : {ℓ : Level} {A : Set ℓ} → ℙ A → ℙ A → Prop ℓ
S ⊆ T = ∀ x → x ∈ S → x ∈ T

-- Equality relation that returns Prop
_≡ᵖ_ : {ℓ : Level} {A : Set ℓ} → ℙ A → ℙ A → Prop
S ≡ᵖ T = ⟪ S ⊆ T ⟫ ∧ᵖ ⟪ T ⊆ S ⟫

-- Subset extensionality
postulate subset-ext : {ℓ : Level} {A : Set ℓ} {S T : ℙ A} → (∀ x → S x ≡ T x) → S ≡ T

⊆-⊇-≡ : {ℓ : Level} {A : Set ℓ} (S T : ℙ A) → S ⊆ T → T ⊆ S → S ≡ T
⊆-⊇-≡ S T S⊆T T⊆S = subset-ext λ x → prop-ext (S⊆T x) (T⊆S x)

-- -- Family of sets
-- data family {ℓ k : Level} : ?
--     -- base :  → (I : Set ℓ) → (A : Set k) → (I → ℙ A)
--     cons : I → A → (I → ℙ A)

set : {ℓ : Level} → (A : Set ℓ) → ℙ A 
set A = λ (x : A) → ⊤ᵖ

-- Union of a family
union : {ℓ k : Level} {I : Set ℓ} {A : Set k} → (I → ℙ A) → ℙ A
union S x = ∃ᵖ (λ i → x ∈ S i)

-- Binary intersection
_∩_ : {ℓ : Level} {A : Set ℓ} → ℙ A → ℙ A → ℙ A
U ∩ V = λ x → U x ∧ᵖ V x

-- Subfamily 
-- subfamily : 
--     {ℓ k : Level} {I J : Set ℓ} {A : Set k} 
--     → (I → ℙ A) 
--     → (set J ⊆ set I)
--     → (J → ℙ A)
-- subfamily = ?

-- Countable set
-- record countable₁ {ℓ} (A : Set ℓ) = Set where 
-- -- ??? Setω₁ 
--     field 
--         ϕ = {!   !}
--         ϕ-injective = {!   !}

ext : ?
ext J = Σ i : I , i ∈ J

-- countable₂ : ?
-- countable₂ A = empty A → ⊤ᵖ
-- countable₂ A = empty A → ⊤ᵖ
