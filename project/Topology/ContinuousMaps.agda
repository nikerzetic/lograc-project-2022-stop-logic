------------------------------------------------------------------------
-- Project: ???
--
-- Continuous maps
------------------------------------------------------------------------

{-# OPTIONS --prop #-}

module Topology.ContinuousMaps where

open import Agda.Primitive
open import Topology.Logic
open import Topology.PowerSet
open import Topology.Core


------------------------------------------------------------------------
 
_∘_ : {ℓ : Level} {X Y Z : Set ℓ} → (g : Y → Z) → (f : X → Y) → (X → Z)
g ∘ f = λ U → g (f U)

preimage : {ℓ : Level} {X Y : Set ℓ} 
   → (f : X → Y)
   → (S : ℙ Y) 
   → ℙ X
preimage f S = λ U → S (f U) 

-- image : {ℓ : Level} {X Y : Set ℓ} 
--     → (f : X → Y) 
--     → ℙ X 
--     → ℙ Y
-- image f X = f X


record continuousMap {ℓ} (X Y : Set ℓ) (f : X → Y) : Setω₁ where
     field
        τ-domain : topology X
        τ-codomain : topology Y
        preimagePreservesOpens : ∀ U → U ∈ (topology.τ τ-codomain) → (preimage f U) ∈ (topology.τ τ-domain) 


compositionOfCountinuousIsContinuous : {ℓ : Level} {X Y Z : Set ℓ} 
  → (f : X → Y) 
  → (continuousMap X Y f)
  → (g : Y → Z) 
  → (continuousMap Y Z g)
  → (continuousMap X Z (g ∘ f)) 
compositionOfCountinuousIsContinuous f fCont g gCont = record
    {
      τ-domain = continuousMap.τ-domain fCont 
    ; τ-codomain = continuousMap.τ-codomain gCont
    ; preimagePreservesOpens = λ U U⊆ᵒZ → 
        ∃ᵖ-elim 
        {!   !} 
        {!   !}
    }

id_ : {ℓ : Level} 
    → (X : Set ℓ)
    → (X → X)
id X = λ (x : X) → x

idIsContinuous : {ℓ : Level} {X : Set ℓ}
    → (T : topology X)
    → (continuousMap X X (id X))
idIsContinuous T = 
    record {
        τ-domain = T
      ; τ-codomain = T
      ; preimagePreservesOpens = {!   !}
    }

record homeomorphism {ℓ} (X Y : Set ℓ) (f : X → Y) (f-1 : Y → X)  : Setω₁ where
    field
      τ-domain : topology X
      τ-codomain : topology Y
      mapsTo : continuousMap X Y f
      mapsFrom : continuousMap Y X f-1

