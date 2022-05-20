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
separated-from : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A B : ℙ ℓ₃ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ {!   !})
separated-from {ℓ₁ = ℓ₁} {X = X} {τ = τ} A B = 
    Σ[ U ∈ ℙ ℓ₁ X ] (topology.Open τ U × A ⊆ U × (U ∩ B ⊆ empty X))

-- Hausdorff space
is-T₂ : {ℓ₀ ℓ₁ ℓ₂ : Level} 
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → {!   !}
is-T₂ X τ = λ (x y : X) → {!   !}
    -- → Σ[ U ∈ topology.Open τ , V ∈ topology.Open τ ] 