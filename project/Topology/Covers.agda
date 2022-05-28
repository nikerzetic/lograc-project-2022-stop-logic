------------------------------------------------------------------------
-- Project: General Topology
--
-- Covers
------------------------------------------------------------------------

module Topology.Covers where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Nullary
open import Topology.PowerSet
open import Topology.Core

------------------------------------------------------------------------

-- Cover of a set
cover : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level} {I : Set ℓ₀} {A : Set ℓ₁} 
    → (I → ℙ ℓ₂ A) → ℙ ℓ₃ A → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
cover {I = I} S B = ∀ x → x ∈ B → Σ[ m ∈ I ] x ∈ S m

-- Open cover of a subset of a topological space
open-cover : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {I : Set ℓ₀} {X : Set ℓ₁} {τ : topology ℓ₂ ℓ₃ X}
    → (S : I → ℙ ℓ₂ X ) → (Y : ℙ ℓ₄ X) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
open-cover {I = I} {τ = τ} S Y = (cover S Y × Σ[ m ∈ I ] topology.Open τ (S m))
    -- Pravilno povedano, da mnozice odprte

-- Subcover of an open cover
subcover : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {I J : Set ℓ₀} {X : Set ℓ₁} {τ : topology ℓ₂ ℓ₃ X}
    → (T : J → ℙ ℓ₃ X) → (S : I → ℙ ℓ₃ X) → (Y : ℙ ℓ₄ X) → {!   !}
subcover {I = I} {J = J} T S Y = {! cover T Y × ∀ m → m ∈ J → Σ[ n ∈ I ] T m ≡ S n !}

