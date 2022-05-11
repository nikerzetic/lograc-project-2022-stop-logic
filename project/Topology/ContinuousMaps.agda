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

-- Proof that (f∘g)(U) = f(g(U)) 
preimageCompose : {ℓ k m : Level} 
    {X : Set ℓ} {Y : Set k} {Z : Set m}
    (f : X → Y) (g : Y → Z)
    (U : ℙ Z)
    → preimage (g ∘ f) U ≡ₛₚ preimage f (preimage g U) 
preimageCompose f g U = reflₛₚ
-- subset-ext (λ x → refl)

-- Image of a map
image : {ℓ k : Level} 
    {X : Set ℓ} {Y : Set k}
    → (f : X → Y)
    → ℙ X
    → ℙ Y
image {X = X} f A = λ y → (∃ᵖ (λ (x : X) → (x ∈ A) ∧ᵖ ((f x) ≡ᵉ y)))

-- Definition for continuous map
isContinuous : {ℓ k : Level} 
    {X : Set ℓ} {Y : Set k} 
    (T₁ : topology X) (T₂ : topology Y) 
    (f : X → Y) 
    → Prop (lsuc lzero ⊔ k)
isContinuous T₁ T₂ f = ∀ U → U ∈ (topology.τ T₂) → (preimage f U) ∈ (topology.τ T₁)

-- Proof that composition of continuous maps is continuous map
compositionOfCountinuousIsContinuous : {ℓ k m : Level} {X : Set ℓ} {Y : Set k} {Z : Set m} 
  {T₁ : topology X} {T₂ : topology Y} {T₃ : topology Z} 
  {f : X → Y} {g : Y → Z}
  → isContinuous T₁ T₂ f
  → isContinuous T₂ T₃ g
  → isContinuous T₁ T₃ (g ∘ f)
compositionOfCountinuousIsContinuous {f = f} {g = g} fCont gCont U U⊆ᵒZ = 
    fCont (preimage g U) (gCont U U⊆ᵒZ)
    -- substᵖ {!   !} (preimageCompose f g U) {!   !}
    -- substᵖ (λ S → S ∈ {!   !}) (preimageCompose f g U) {!   !}

-- Identity map on a set X
id_ : {ℓ : Level} 
    → (X : Set ℓ)
    → (X → X)
id X = λ (x : X) → x

-- Proof that identity map is continuous
idIsContinuous : {ℓ : Level} {X : Set ℓ} 
    {T : topology X} 
    → isContinuous T T (id X)
idIsContinuous = λ _ U⊆ᵒX → U⊆ᵒX

-- Constant map from a set X to * ∈ Y
constF : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
    → (* : Y)
    → (X → Y)
constF * = λ x → *

-- Proof that constant map is continuous
emptyPreimage : {ℓ k : Level} {X : Set ℓ} {Y : Set k} (U : ℙ Y) (* : Y) → ℙ X
emptyPreimage U * = preimage (constF *) (U ∩ singelton *)

constIsContinuous : {ℓ k : Level} {X : Set ℓ} {Y : Set k} 
    {T₁ : topology X} {T₂ : topology Y}
    → (* : Y) 
    → isContinuous T₁ T₂ (constF *)
constIsContinuous {X = X} {T₁ = T₁} * = λ U U⊆ᵒY →
    ∨ᵖ-elim (∉∈Set U *) 
        (λ *∈U → {!   !}) 
        (λ *∉U → {!   !})
        -- (λ *∈U → {! full X ∈ topology.τ T₁  !}) 
        -- (λ *∉U → {! empty X ∈ topology.τ T₁  !})

-- vsaka preslikava iz prostora z diskretno topologijo je zvezna
fromDiscreteContinuous : {ℓ k : Level} {X : Set ℓ} {Y : Set k} 
    → {T : topology Y}
    → (f : X → Y)
    → isContinuous (discrete-topology X) T f
fromDiscreteContinuous f = λ U U⊆ᵒY → ⊤ᵖ-intro

-- vsaka preslikava v prostor s trivialno topologijo je zvezna TODO
toIndiscreteContinuous : {ℓ k : Level} {X : Set ℓ} {Y : Set k} 
    → {T : topology X}
    → (f : X → Y)
    → isContinuous T (indiscrete-topology Y) f
toIndiscreteContinuous {T = T} f = λ U U⊆ᵒY → 
    {!  !}

-- Surjectivity, Injectivity and Bijectivity
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

-- Definition of a homeomorphism
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