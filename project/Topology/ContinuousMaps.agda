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

-- -- Function image and preimage
-- _ₓ_ : {!  {ℓ : Level} {X Y : Set ℓ} → (f : X → Y) → ℙ X !}
-- f ₓ U = {!   !}

-- _ˣ_ : {!   !}
-- f ˣ V = {!   !} 

preimage : {ℓ : Level} {X Y : Set ℓ} 
   → (f : (ℙ X) → (ℙ Y))
   → {f^-1 : (ℙ Y) → (ℙ X)}
   → {∀ (U : ℙ Y) → ((f (f^-1 U)) ≡ᵖ U)}
   → ℙ Y 
   → ℙ X
preimage f {f-1} Y = f-1 Y

image : {ℓ : Level} → {X Y : Set ℓ} → (f : (ℙ X) → (ℙ Y)) → ℙ X → ℙ Y
image f X = f X

_∘_ : {ℓ : Level} {X Y Z : Set ℓ} → (g : ℙ Y → ℙ Z) → (f : ℙ X → ℙ Y) → (ℙ X → ℙ Z)
g ∘ f = λ U → g (f U)

record continuous-map {ℓ} (X Y : Set ℓ) (f : (ℙ X) → (ℙ Y)) : Setω₁ where
     field
        τ-domain : topology X
        τ-codomain : topology Y
        preimagePreservesOpens : ∀ U → U ∈ (topology.τ τ-codomain) → (preimage f U) ∈ (topology.τ τ-domain) 


compositionOfCountinuousIsContinuous : {ℓ : Level} {X Y Z : Set ℓ} 
  → (f : ℙ X → ℙ Y) 
  → (continuous-map X Y f)
  → (g : ℙ Y → ℙ Z) 
  → (continuous-map Y Z g)
  → (continuous-map X Z (g ∘ f)) 
compositionOfCountinuousIsContinuous f fCont g gCont = record
    {
      τ-domain = continuous-map.τ-domain fCont 
    ; τ-codomain = continuous-map.τ-codomain gCont
    ; preimagePreservesOpens = {!   !}
    }