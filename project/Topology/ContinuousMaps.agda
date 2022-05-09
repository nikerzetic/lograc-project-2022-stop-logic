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
open import Relation.Binary.PropositionalEquality


------------------------------------------------------------------------
 
_∘_ : {ℓ k m : Level} {X : Set ℓ} {Y : Set k} {Z : Set m} → (g : Y → Z) → (f : X → Y) → (X → Z)
g ∘ f = λ U → g (f U)

preimage : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
   → (f : X → Y)
   → (S : ℙ Y) 
   → ℙ X
preimage f S = S ∘ f

preimageCompose : {ℓ k m : Level} 
    {X : Set ℓ} {Y : Set k} {Z : Set m}
    (f : X → Y) (g : Y → Z)
    (U : ℙ Z)
    → preimage (g ∘ f) U ≡ₛₚ preimage f (preimage g U) 
preimageCompose f g U = reflₛₚ
-- subset-ext (λ x → refl)

image : {ℓ k : Level} 
    {X : Set ℓ} {Y : Set k}
    → (f : X → Y)
    → ℙ X
    → ℙ Y
image {X = X} f A = λ y → (∃ᵖ (λ (x : X) → (x ∈ A) ∧ᵖ ((f x) ≡ᵉ y)))

isContinuous : {ℓ k : Level} 
    {X : Set ℓ} {Y : Set k} 
    (T₁ : topology X) (T₂ : topology Y) 
    (f : X → Y) 
    → Prop (lsuc lzero ⊔ k)
isContinuous T₁ T₂ f = ∀ U → U ∈ (topology.τ T₂) → (preimage f U) ∈ (topology.τ T₁)

compositionOfCountinuousIsContinuous : {ℓ k m : Level} {X : Set ℓ} {Y : Set k} {Z : Set m} 
  {T₁ : topology X} {T₂ : topology Y} {T₃ : topology Z} 
  {f : X → Y} {g : Y → Z}
  → isContinuous T₁ T₂ f
  → isContinuous T₂ T₃ g
  → isContinuous T₁ T₃ (g ∘ f)
compositionOfCountinuousIsContinuous {f = f} {g = g} fCont gCont U U⊆ᵒZ = 
    substᵖ (λ S → S ∈ {!   !}) (preimageCompose f g U) {!   !}

id_ : {ℓ : Level} 
    → (X : Set ℓ)
    → (X → X)
id X = λ (x : X) → x

idIsContinuous : {ℓ : Level} {X : Set ℓ} 
    {T : topology X} 
    → isContinuous T T (id X)
idIsContinuous = λ _ U⊆ᵒX → U⊆ᵒX

const : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
    → (* : Y)
    → (X → Y)
const * = λ x → *

constF : {ℓ k : Level} {X : Set ℓ} {Y : Set k} 
    {T₁ : topology X} {T₂ : topology Y}
    → (* : Y) 
    → isContinuous T₁ T₂ (const *)
constF {X = X} {T₁ = T₁} * = λ U U⊆ᵒY → 
    -- Ločimo dva primera
    {!   !}

isSurjective : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
    → (f : X → Y)
    → Prop k
isSurjective {X = X} {Y = Y} f = ∀ y → y ∈ full Y → ∃ᵖ (λ (x : X) → (f x) ≡ᵉ y)

isInjective : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
    → (f : X → Y)
    → Prop ℓ
isInjective {X = X} {Y = Y} f = 
    ∀ x₁ → x₁ ∈ full X → 
        ∀ x₂ → x₂ ∈ full X → (¬ᵖ (x₁ ≡ᵉ x₂)) ⇒ᵖ (¬ᵖ ((f x₁) ≡ᵉ (f x₂)))

isBijective : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
    → (f : X → Y)
    → Prop 
isBijective f = ⟪ isInjective f ⟫ ∧ᵖ ⟪ isSurjective f ⟫

isHomeomorphism : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
    (T₁ : topology X) (T₂ : topology Y)
    → (f : X → Y)
    → Prop
isHomeomorphism T₁ T₂ f = 
    (⟪ isContinuous T₁ T₂ f ⟫ 
    ∧ᵖ 
    ⟪ (∀ U → U ∈ (topology.τ T₁) → (image f U ∈ (topology.τ T₂))) ⟫) -- open map
    ∧ᵖ
    isBijective f
-----------
-- record continuousMap {ℓ} (X Y : Set ℓ) (f : X → Y) : Setω₁ where
--      field
--         τ-domain : topology X
--         τ-codomain : topology Y
--         preimagePreservesOpens : ∀ U → U ∈ (topology.τ τ-codomain) → (preimage f U) ∈ (topology.τ τ-domain) -- lahko posebej funkcijo


-- compositionOfCountinuousIsContinuous : {ℓ : Level} {X Y Z : Set ℓ} 
--   → (f : X → Y) 
--   → (continuousMap X Y f)
--   → (g : Y → Z) 
--   → (continuousMap Y Z g)
--   → (continuousMap X Z (g ∘ f)) 
-- compositionOfCountinuousIsContinuous f fCont g gCont = record
--     {
--       τ-domain = continuousMap.τ-domain fCont 
--     ; τ-codomain = continuousMap.τ-codomain gCont
--     ; preimagePreservesOpens = λ U U⊆ᵒZ → 
--         ∃ᵖ-elim 
--         {!   !} 
--         {!   !}
--     }

-- id_ : {ℓ : Level} 
--     → (X : Set ℓ)
--     → (X → X)
-- id X = λ (x : X) → x

-- idIsContinuous : {ℓ : Level} {X : Set ℓ}
--     → (T : topology X)
--     → (continuousMap X X (id X))
-- idIsContinuous T = 
--     record {
--         τ-domain = T
--       ; τ-codomain = T
--       ; preimagePreservesOpens = λ U U⊆ᵒX → {!  !}
--     }

-- record homeomorphism {ℓ} (X Y : Set ℓ) (f : X → Y) (f-1 : Y → X)  : Setω₁ where
--     field
--       τ-domain : topology X
--       τ-codomain : topology Y
--       mapsTo : continuousMap X Y f
--       mapsFrom : continuousMap Y X f-1

 