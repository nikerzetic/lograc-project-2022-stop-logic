------------------------------------------------------------------------
-- Project: ???
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

_∘_ : {ℓ k m : Level} {X : Set ℓ} {Y : Set k} {Z : Set m} → (g : Y → Z) → (f : X → Y) → (X → Z)
g ∘ f = λ U → g (f U)


preimage : {ℓ k m : Level} {X : Set ℓ} {Y : Set k}
   → (f : X → Y)
   → (S : ℙ m Y)
   → ℙ m X
preimage f S = S ∘ f

-- Proof that (f∘g)(U) = f(g(U))
preimageCompose : {ℓ k m n : Level}
    {X : Set ℓ} {Y : Set k} {Z : Set m}
    (f : X → Y) (g : Y → Z)
    (U : ℙ n Z)
    → preimage (g ∘ f) U ≡ preimage f (preimage g U)
preimageCompose f g U = refl

-- Image of a map
image : {ℓ k m : Level}
    {X : Set ℓ} {Y : Set k}
    → (f : X → Y)
    → ℙ m X
    → ℙ (ℓ ⊔ k ⊔ m) Y
image {X = X} {Y = Y} f A y = Σ[ x ∈ X ] (A x × y ≡ (f x))

-- Definition for continuous map
isContinuous : {ℓ k m n₁ n₂ : Level}
    {X : Set ℓ} {Y : Set k}
    (T₁ : topology m n₁ X) (T₂ : topology m n₂ Y)
    (f : X → Y)
    → Set (k ⊔ lsuc m ⊔ n₁ ⊔ n₂)
isContinuous T₁ T₂ f = ∀ U → U ∈ (Open T₂) → (preimage f U) ∈ (Open T₁)

-- Proof that composition of continuous maps is continuous map
compositionOfCountinuousIsContinuous : {ℓ k m j n₁ n₂ n₃ : Level} {X : Set ℓ} {Y : Set k} {Z : Set m}
  {T₁ : topology j n₁ X} {T₂ : topology j n₂ Y} {T₃ : topology j n₃ Z}
  {f : X → Y} {g : Y → Z}
  → isContinuous T₁ T₂ f
  → isContinuous T₂ T₃ g
  → isContinuous T₁ T₃ (g ∘ f)
compositionOfCountinuousIsContinuous {f = f} {g = g} fCont gCont U U⊆ᵒZ =
    fCont (preimage g U) (gCont U U⊆ᵒZ)

-- Identity map on a set X
id_ : {ℓ : Level}
    → (X : Set ℓ)
    → (X → X)
id X = λ (x : X) → x

-- Proof that identity map is continuous
idIsContinuous : {ℓ m n : Level} {X : Set ℓ}
    {T : topology m n X}
    → isContinuous T T (id X)
idIsContinuous = λ _ U⊆ᵒX → U⊆ᵒX

-- Constant map from a set X to * ∈ Y
constF : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
    → (* : Y)
    → (X → Y)
constF * = λ x → *

-- Proof that constant map is continuous
emptyFullPreimage : {ℓ k m : Level} {X : Set ℓ} {Y : Set k} (U : ℙ m Y) (* : Y) → ℙ (k ⊔ m) X
emptyFullPreimage U * = preimage (constF *) (U ∩ singelton *)

constIsContinuous : {ℓ k m n : Level} {X : Set ℓ} {Y : Set k}
    {T₁ : topology m n X} {T₂ : topology m n Y}
    → (* : Y)
    → isContinuous T₁ T₂ (constF *)
constIsContinuous {ℓ} {k} {m} {n} {X = X} {T₁ = T₁} {T₂ = T₂} * U Uopen =
  subst (Open T₁) V≡pre OpenV
  where 
    V : ℙ m X
    V = union {I = U *} {A = X} λ _ → full X

    OpenV : Open T₁ V
    OpenV = union-open T₁ (λ _ → full X) (λ i → full-open T₁)

    V≡pre : V ≡ (λ _ → U *)
    V≡pre = ⊆-⊇-≡ V (λ _ → U *) (λ x (x∈U* , _) → x∈U*) λ x p → p , full-intro
    

-- vsaka preslikava iz prostora z diskretno topologijo je zvezna
fromDiscreteContinuous : {ℓ k m n : Level} {X : Set ℓ} {Y : Set k}
    → {T : topology m n Y}
    → (f : X → Y)
    → isContinuous (discrete-topology X) T f
fromDiscreteContinuous f = λ U U⊆ᵒY → ⊤ℓ-intro


-- vsaka preslikava v prostor s trivialno topologijo je zvezna
-- Za index set uporabljamo "Y ⊆ U"
-- toIndiscreteContinuous : {m : Level} {X : Set m} {Y : Set m}
--     → {T : topology m lzero X}
--     → (f : X → Y)
--     → isContinuous T (indiscrete-topology Y) f
-- toIndiscreteContinuous {m} {X = X} {Y = Y} {T = T} f U U⊆ᵒY =  
--     subst (Open T) V≡pre-fU OpenV
--     where 
--     V : ℙ m X
--     V = union {I = (full {k = m} Y) ⊆ U} λ _ → full X

--     OpenV : Open T V
--     OpenV = union-open T (λ _ → full X) λ i → full-open T

--     V≡pre-fU : V ≡ (λ x → U (f x))
--     V≡pre-fU = ⊆-⊇-≡ 
--         V 
--         (λ x → U (f x)) 
--         (λ x x∈V → proj₁ x∈V (f x) full-intro) 
--         (λ x p → (λ y _ → U⊆ᵒY (f x) p y) , full-intro)

-- Same thing, with index set "there exists an element in U". 
-- Here, we can have different level of set X
toIndiscreteContinuous : {ℓ m : Level} {X : Set ℓ} {Y : Set m}
    → {T : topology m lzero X}
    → (f : X → Y)
    → isContinuous T (indiscrete-topology Y) f
toIndiscreteContinuous {ℓ} {m} {X = X} {Y = Y} {T = T} f U U⊆ᵒY =  
    -- subst (Open T) V≡pre-fU OpenV
    subst (Open T) V≡pre-fU (OpenV)
    where 
    V : ℙ m X
    V = union {I = Σ[ y ∈ Y ] y ∈ U} λ _ → full {k = m} X

    OpenV : Open T V
    OpenV = union-open T (λ _ → full X) (λ i → full-open T)

    V≡pre-fU : V ≡ (λ x → U (f x))
    V≡pre-fU = ⊆-⊇-≡ 
        V 
        (λ x → U (f x)) 
        (λ x ((p₁ , p₂) , q) → U⊆ᵒY p₁ p₂ (f x))
        (λ x p → (f x , p) , full-intro)


-- Definition of a homeomorphism
isHomeomorphism : {ℓ k m n o : Level} {X : Set ℓ} {Y : Set k}
    → (T₁ : topology m n X) (T₂ : topology m o Y) 
    → (f : X → Y)
    → (g : Y → X)
    → Set (ℓ ⊔ k ⊔ lsuc m ⊔ n ⊔ o)
isHomeomorphism {ℓ = ℓ} {k = k} {X = X} {Y = Y} T₁ T₂ f g = 
    (isContinuous T₁ T₂ f) ×
    (isContinuous T₂ T₁ g) ×
    (∀ x → x ∈ full {k = ℓ} X → (g ∘ f) x ≡ x) × 
    (∀ y → y ∈ full {k = k} Y → (f ∘ g) y ≡ y)

inverseOfHomeoIsHomeo : {ℓ k m n o : Level} {X : Set ℓ} {Y : Set k}
    → {T₁ : topology m n X} {T₂ : topology m o Y}
    → (f : X → Y)
    → (g : Y → X)
    → isHomeomorphism T₁ T₂ f g
    → isHomeomorphism T₂ T₁ g f
inverseOfHomeoIsHomeo f g (fCont , gCont , gfx=x , fgx=x) = 
      gCont 
    , (fCont 
    , ((λ x _ → fgx=x x full-intro) 
    , (λ y _ → gfx=x y full-intro)))

idIsHomeo : {ℓ m n : Level} {X : Set ℓ}
    → {T : topology m n X}
    → isHomeomorphism T T (id X) (id X)
idIsHomeo {X = X} {T = T} = 
      idIsContinuous {X = X} {T = T} 
    , (idIsContinuous {X = X} {T = T} 
    , ((λ x _ → refl) 
    , λ y _ → refl))

compositionOfHomeoIsHomeo : {a b c d e i j : Level}
    → {X : Set a} {Y : Set b} {Z : Set c}
    → {T₁ : topology d e X} {T₂ : topology d i Y} {T₃ : topology d j Z}
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
