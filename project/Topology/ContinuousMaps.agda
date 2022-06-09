------------------------------------------------------------------------
-- Project: General Topology
--
-- Continuous maps
------------------------------------------------------------------------


module Topology.ContinuousMaps where

open import Agda.Primitive
open import Topology.PowerSet
open import Data.Product
open import Topology.Core
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

------------------------------------------------------------------------

private
    variable
        ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

------------------------------------------------------------------------
preimage : {X : Set ℓ₀} {Y : Set ℓ₁}
   → (f : X → Y)
   → (S : ℙ ℓ₂ Y)
   → ℙ ℓ₂ X
preimage f S = S ∘ f

-- Proof that (f∘g)(U) = f(g(U))
preimageCompose : {X : Set ℓ₀} {Y : Set ℓ₁} {Z : Set ℓ₂}
    (f : X → Y) (g : Y → Z)
    (U : ℙ ℓ₃ Z)
    → preimage (g ∘ f) U ≡ preimage f (preimage g U)
preimageCompose f g U = refl

-- Image of a map
image : {X : Set ℓ₀} {Y : Set ℓ₁}
    → (f : X → Y)
    → ℙ ℓ₂ X
    → ℙ (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) Y
image {X = X} {Y = Y} f A y = Σ[ x ∈ X ] (A x × y ≡ (f x))

-- Definition of continuous map
isContinuous : {X : Set ℓ₀} {Y : Set ℓ₁}
    (T₁ : topology ℓ₂ ℓ₃ X) (T₂ : topology ℓ₂ ℓ₄ Y)
    (f : X → Y)
    → Set (ℓ₁ ⊔ lsuc ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
isContinuous T₁ T₂ f = ∀ U → U ∈ (Open T₂) → (preimage f U) ∈ (Open T₁)

-- Proof that composition of continuous maps is a continuous map
compositionOfCountinuousIsContinuous : {X : Set ℓ₀} {Y : Set ℓ₁} {Z : Set ℓ₂}
  {T₁ : topology ℓ₆ ℓ₃ X} {T₂ : topology ℓ₆ ℓ₄ Y} {T₃ : topology ℓ₆ ℓ₅ Z}
  {f : X → Y} {g : Y → Z}
  → isContinuous T₁ T₂ f
  → isContinuous T₂ T₃ g
  → isContinuous T₁ T₃ (g ∘ f)
compositionOfCountinuousIsContinuous {f = f} {g = g} fCont gCont U U⊆ᵒZ =
    fCont (preimage g U) (gCont U U⊆ᵒZ)

-- Identity map on a set X
id_ : (X : Set ℓ₀) → (X → X)
id X = λ (x : X) → x

-- Proof that identity map is continuous
idIsContinuous : {X : Set ℓ₀} {T : topology ℓ₁ ℓ₂ X}
    → isContinuous T T (id X)
idIsContinuous = λ _ U⊆ᵒX → U⊆ᵒX

-- Constant map from a set X to * ∈ Y
constF : {X : Set ℓ₀} {Y : Set ℓ₁}
    → (* : Y)
    → (X → Y)
constF * = λ x → *

-- Proof that constant map is continuous
constIsContinuous : {X : Set ℓ₀} {Y : Set ℓ₁}
    {T₁ : topology ℓ₂ ℓ₃ X} {T₂ : topology ℓ₂ ℓ₃ Y}
    → (* : Y)
    → isContinuous T₁ T₂ (constF *)
constIsContinuous {ℓ₂ = ℓ₂} {X = X} {T₁ = T₁} {T₂ = T₂} * U Uopen =
  subst (Open T₁) V≡pre OpenV
  where 
    V : ℙ ℓ₂ X
    V = union {I = U *} {A = X} λ _ → full X

    OpenV : Open T₁ V
    OpenV = union-open T₁ (λ _ → full X) (λ i → full-open T₁)

    V≡pre : V ≡ (λ _ → U *)
    V≡pre = ⊆-⊇-≡ V (λ _ → U *) (λ x (x∈U* , _) → x∈U*) λ x p → p , full-intro
    
-- Proof that every map from a space with discrete topology is continuous
fromDiscreteContinuous : {X : Set ℓ₀} {Y : Set ℓ₁} {T : topology ℓ₂ ℓ₃ Y}
    → (f : X → Y)
    → isContinuous (discrete-topology X) T f
fromDiscreteContinuous f = λ U U⊆ᵒY → ⊤ℓ-intro

-- Proof that every map to trivial topology is continuous
-- index set : codomain is subset of open set
toIndiscreteContinuous : {X : Set ℓ₀} {Y : Set ℓ₀} {T : topology ℓ₀ ℓ₁ X}
    → (f : X → Y)
    → isContinuous T (indiscrete-topology Y) f
toIndiscreteContinuous {ℓ₀} {X = X} {Y = Y} {T = T} f U U⊆ᵒY =  
    subst (Open T) V≡pre-fU OpenV
    where 
    V : ℙ ℓ₀ X
    V = union {I = (full {k = ℓ₀} Y) ⊆ U} λ _ → full X

    OpenV : Open T V
    OpenV = union-open T (λ _ → full X) λ i → full-open T

    V≡pre-fU : V ≡ (λ x → U (f x))
    V≡pre-fU = ⊆-⊇-≡ 
        V 
        (λ x → U (f x)) 
        (λ x x∈V → proj₁ x∈V (f x) full-intro) 
        (λ x p → (λ y _ → U⊆ᵒY (f x) p y) , full-intro)

-- Proof that every map to trivial topology is continuous second edition
-- index set : there exists an element in open set
toIndiscreteContinuous' : {X : Set ℓ₀} {Y : Set ℓ₁} {T : topology ℓ₁ ℓ₂ X}
    → (f : X → Y)
    → isContinuous T (indiscrete-topology Y) f
toIndiscreteContinuous' {ℓ₁ = ℓ₁} {X = X} {Y = Y} {T = T} f U U⊆ᵒY =  
    subst (Open T) V≡pre-fU OpenV
    where 
    V : ℙ ℓ₁ X
    V = union {I = Σ[ y ∈ Y ] y ∈ U} λ _ → full {k = ℓ₁} X

    OpenV : Open T V
    OpenV = union-open T (λ _ → full X) (λ i → full-open T)

    V≡pre-fU : V ≡ (λ x → U (f x))
    V≡pre-fU = ⊆-⊇-≡ 
        V 
        (λ x → U (f x)) 
        (λ x ((p₁ , p₂) , q) → U⊆ᵒY p₁ p₂ (f x))
        (λ x p → (f x , p) , full-intro)

-- Definition of a homeomorphism
isHomeomorphism : {X : Set ℓ₀} {Y : Set ℓ₁}
    → (T₁ : topology ℓ₂ ℓ₃ X) (T₂ : topology ℓ₂ ℓ₄ Y) 
    → (f : X → Y)
    → (g : Y → X)
    → Set (ℓ₀ ⊔ ℓ₁ ⊔ lsuc ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
isHomeomorphism {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {X = X} {Y = Y} T₁ T₂ f g = 
    (isContinuous T₁ T₂ f) ×
    (isContinuous T₂ T₁ g) ×
    (∀ x → x ∈ full {k = ℓ₀} X → (g ∘ f) x ≡ x) × 
    (∀ y → y ∈ full {k = ℓ₁} Y → (f ∘ g) y ≡ y)

-- Construction of an inverse of a homeomorphism
inverseOfHomeoIsHomeo : {X : Set ℓ₀} {Y : Set ℓ₁}
    → {T₁ : topology ℓ₂ ℓ₃ X} {T₂ : topology ℓ₂ ℓ₄ Y}
    → (f : X → Y)
    → (g : Y → X)
    → isHomeomorphism T₁ T₂ f g
    → isHomeomorphism T₂ T₁ g f
inverseOfHomeoIsHomeo f g (fCont , gCont , gfx=x , fgx=x) = 
      gCont 
    , (fCont 
    , ((λ x _ → fgx=x x full-intro) 
    , (λ y _ → gfx=x y full-intro)))

-- Proof that identity map is a homeomorphism
idIsHomeo : {X : Set ℓ₀} {T : topology ℓ₁ ℓ₂ X}
    → isHomeomorphism T T (id X) (id X)
idIsHomeo {X = X} {T = T} = 
      idIsContinuous {X = X} {T = T} 
    , (idIsContinuous {X = X} {T = T} 
    , ((λ x _ → refl) 
    , λ y _ → refl))

-- Proof that composition of homeomorphisms is again homeomorphism
compositionOfHomeoIsHomeo : {X : Set ℓ₀} {Y : Set ℓ₁} {Z : Set ℓ₂}
    → {T₁ : topology ℓ₃ ℓ₄ X} {T₂ : topology ℓ₃ ℓ₅ Y} {T₃ : topology ℓ₃ ℓ₆ Z}
    → (f : X → Y) (g : Y → Z)
    → (f-1 : Y → X) (g-1 : Z → Y)
    → isHomeomorphism T₁ T₂ f f-1
    → isHomeomorphism T₂ T₃ g g-1
    → isHomeomorphism T₁ T₃ (g ∘ f) (f-1 ∘ g-1)
compositionOfHomeoIsHomeo 
  {X = X} {Z = Z} f g f-1 g-1 (fCont , f-1Cont , f-1fx=x , ff-1x=x) (gCont , g-1Cont , g-1gx=x , gg-1x=x) = 
      (λ U OpenU → fCont (preimage g U) (gCont U OpenU)) 
    , ((λ U OpenU → g-1Cont (preimage f-1 U) (f-1Cont U OpenU))
    , (compose-gf
    , compose-f-1g-1))
  where 
  compose-gf : (x : X) → x ∈ full X → ((f-1 ∘ g-1) ∘ (g ∘ f)) x ≡ x
  compose-gf = λ x _ → 
    begin
      ((f-1 ∘ g-1) ∘ (g ∘ f)) x ≡⟨ refl ⟩
      f-1 ( g-1 (g ( f x))) ≡⟨ cong f-1 (g-1gx=x (f x) full-intro) ⟩
      f-1 (f x) ≡⟨ f-1fx=x x full-intro ⟩  
      x
    ∎

  compose-f-1g-1 : (y : Z) → y ∈ full Z → ((g ∘ f) ∘ (f-1 ∘ g-1)) y ≡ y
  compose-f-1g-1 = λ y _ → 
    begin
      ((g ∘ f) ∘ (f-1 ∘ g-1)) y ≡⟨ refl ⟩
      g ( f (f-1 ( g-1 y))) ≡⟨ cong g (ff-1x=x (g-1 y) full-intro) ⟩
      g (g-1 y) ≡⟨ gg-1x=x y full-intro ⟩  
      y
    ∎
 