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

-- Function image and preimage
_ₓ_ : {!  {ℓ : Level} {X Y : Set ℓ} → (f : X → Y) → ℙ X !}
f ₓ U = {!   !}

_ˣ_ : {!   !}
f ˣ V = {!   !} 

-- record continuous-map {ℓ} (X Y : Set ℓ) (f : X → Y) : Setω₁ where
--      field
--         τ-domain : topology X
--         τ-codomain : topology Y
--         preimage-preserves-opens : ∀ U → U ∈ τ-codomain.τ → f ^* U ∈ τ-domain 

--         f_* (f^* A) = A
        