------------------------------------------------------------------------
-- Project ???
--
-- Properties
------------------------------------------------------------------------

module Topology.Properties where

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

-- Sets separated by neighbourhoods 
separated-from : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (A : ℙ ℓ₄ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
separated-from {ℓ₁ = ℓ₁} {ℓ₅ = ℓ₅} {X = X} {τ = τ} A B = 
    Σ[ U ∈ ℙ ℓ₁ X ] (topology.Open τ U × A ⊆ U × (U ∩ B ⊆ empty {k = ℓ₅} X))

-- Separated sets
separated : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (A : ℙ ℓ₄ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
separated {ℓ₁ = ℓ₁} {ℓ₅ = ℓ₅} {X = X} {τ = τ} A B = 
    Σ[ U ∈ ℙ ℓ₁ X ] (Σ[ V ∈ ℙ ℓ₁ X ] A ⊆ U × B ⊆ V × U ∩ V ⊆ empty {k = ℓ₅} X)

------------------------------------------------------------------------
-- Separation axioms

-- Kolmogorov space
-- is-T₀ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
--     → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → {!   !}
-- is-T₀ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
--     → ¬ singleton x ≡ singleton y
--     → separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y) ∨ 
--     separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton y) (singleton x)

-- Frechet space
is-T₀ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-T₀ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ singleton x ≡ singleton y
    → separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y) × 
    separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton y) (singleton x)

-- Hausdorff space
is-T₂ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₃)
is-T₂ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ singleton x ≡ singleton y
    → separated {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y)
