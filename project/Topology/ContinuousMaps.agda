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
   → (f : (ℙ X) →  (ℙ Y))
   → {f^-1 : (ℙ Y) →  (ℙ X)}
   → {∀ (U : ℙ Y) → ((f (f^-1 U)) ≡ᵖ U)}
   → ℙ Y 
   → ℙ X
preimage f {f-1} Y = f-1 Y

image : {ℓ : Level} → {X Y : Set ℓ} → (f : (ℙ X) → (ℙ Y)) → ℙ X → ℙ Y
image f X = f X

record continuous-map {ℓ} (X Y : Set ℓ) (f : (ℙ X) → (ℙ Y)) : Setω₁ where
     field
        τ-domain : topology X
        τ-codomain : topology Y
        preimagePreservesOpens : ∀ U → U ∈ (topology.τ τ-codomain) → (preimage f U) ∈ (topology.τ τ-domain) 


