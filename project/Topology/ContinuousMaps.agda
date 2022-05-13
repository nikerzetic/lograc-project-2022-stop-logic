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
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Unit


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
-- λ (y : Y) → (∃ (λ (x : X) → ((x ∈ A) ∧ᵖ (singelton (f x) ≡ᵖ singelton y))))

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

-- Druzina indeksirana z dokazi p-ja
cow : {ℓ m : Level} {X : Set ℓ} → (p : Set) → p → ℙ m X
cow {X = X} p _ = full X

constIsContinuous : {ℓ k m n : Level} {X : Set ℓ} {Y : Set k}
    {T₁ : topology m n X} {T₂ : topology m n Y}
    → (* : Y)
    → isContinuous T₁ T₂ (constF *)
constIsContinuous {ℓ} {k} {m} {n} {X = X} {T₁ = T₁} {T₂ = T₂} * U Uopen =
  subst (Open T₁) V≡pre OpenV
  where
    V : ℙ m X
    V = union {I = U *} {A = X} (λ _ → full {k = m} X)

    OpenV : Open T₁ V
    OpenV = union-open T₁ ((λ _ → full {k = m} X)) λ i → full-open T₁

    V≡pre : V ≡ (λ _ → U *)
    V≡pre = ⊆-⊇-≡ V (λ _ → U *) (λ { x (x∈U* , _) → x∈U* }) (λ x p → p , full-intro)




-- vsaka preslikava iz prostora z diskretno topologijo je zvezna
fromDiscreteContinuous : {ℓ k m n : Level} {X : Set ℓ} {Y : Set k}
    → {T : topology m n Y}
    → (f : X → Y)
    → isContinuous (discrete-topology X) T f
fromDiscreteContinuous f = λ U U⊆ᵒY → ⊤ℓ-intro

-- vsaka preslikava v prostor s trivialno topologijo je zvezna TODO
toIndiscreteContinuous : {ℓ k m n : Level} {X : Set ℓ} {Y : Set k}
    → {T : topology m n X}
    → (f : X → Y)
    → isContinuous T (indiscrete-topology Y) f
toIndiscreteContinuous {T = T} f = λ U U⊆ᵒY → {!   !}


-- record _≃_ {ℓ m : Level} (A : Set ℓ) (B : Set m) : Set (ℓ ⊔ m) where
--   field
--     to      : A → B
--     from    : B → A
--     from∘to : (x : A) → from (to x) ≡ x
--     to∘from : (y : B) → to (from y) ≡ y

--     toCont : {!  isContinuous  !}
--     fromCont : {!   !}

-- -- Definition of a homeomorphism
-- isHomeomorphism : {ℓ k m n₁ n₂ : Level} {X : Set ℓ} {Y : Set k}
--     (T₁ : topology m n₁ X) (T₂ : topology m n₂ Y)
--     → (f : X → Y)
--     → (g : Y → X)
--     → contf , contg , X
-- isHomeomorphism {X = X} {Y = Y} T₁ T₂ f g = (isContinuous T₁ T₂ f) × (isContinuous T₂ T₁ g) × X≃Y
--                             where
--                             X≃Y : X ≃ Y
--                             X≃Y = ?


-- -- Surjectivity, Injectivity and Bijectivity
-- isSurjective : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
--     → (f : X → Y)
--     → Set k
-- isSurjective {X = X} {Y = Y} f = ∀ y → y ∈ full Y → ∃ᵖ (λ (x : X) → (f x) ≡ᵉ y)


-- isInjective : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
--     → (f : X → Y)
--     → Set ℓ
-- isInjective {X = X} {Y = Y} f =
--     ∀ x₁ → x₁ ∈ full X →
--         ∀ x₂ → x₂ ∈ full X → (f x₁) ≡ᵉ (f x₂) → x₁ ≡ᵉ x₂


-- isBijective : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
--     → (f : X → Y)
--     → Set
-- isBijective f = ⟪ isInjective f ⟫ ∧ᵖ ⟪ isSurjective f ⟫

-- -- Definition of a homeomorphism
-- isHomeomorphism : {ℓ k : Level} {X : Set ℓ} {Y : Set k}
--     (T₁ : topology X) (T₂ : topology Y)
--     → (f : X → Y)
--     → Set
-- isHomeomorphism T₁ T₂ f =
--     (⟪ isContinuous T₁ T₂ f ⟫
--     ∧ᵖ
--     ⟪ (∀ U → U ∈ (topology.τ T₁) → (image f U ∈ (topology.τ T₂))) ⟫) -- open map
--     ∧ᵖ
--     isBijective f

-- -- Lemma: Under identity map image is the same as original
-- idX=X : {ℓ : Level}
--     → {X : Set ℓ}
--     → {U : ℙ X}
--     → image (id X) U ≡ U
-- idX=X {U} = subset-ext λ x → prop-ext
--     -- (λ x∈image → ∃ᵖ-elim ∧ᵖ-elim₁ {!   !})
--     (λ xInImage → {!   !})
--     λ x∈U →
--       ↓ (∃-intro
--         (∧ᵖ-intro
--           x∈U
--           (∧ᵖ-intro
--             (∀ᵖ-intro (λ x₁ x₁∈sx → x₁∈sx))
--             (∀ᵖ-intro (λ x₁ x₁∈sx → x₁∈sx))
--           )
--         )
--         )


-- idIsHomeomorphism : {ℓ : Level} {X : Set ℓ} {T : topology X} → isHomeomorphism T T (id X)
-- idIsHomeomorphism {ℓ = ℓ} {X = X} {T = T} =
--     ∧ᵖ-intro
--       (∧ᵖ-intro
--         (∀ᵖ-intro (idIsContinuous {ℓ} {X} {T})) -- continuous
--         (∀ᵖ-intro (λ U Uopen → {!   !}
--           ))
-- --         (∀ᵖ-intro λ U Uopen →
-- --           topology.union-open
-- --           T
-- --           (λ z z₁ →
-- --             z ∈ U
-- --             ∧ᵖ
-- --             (
-- --               ⟪ ((x : X) (x₁ : x ≡ᵉ z) → x ≡ᵉ z₁) ⟫
-- --               ∧ᵖ
-- --               ⟪ ((x : X) (x₁ : x ≡ᵉ z₁) → x ≡ᵉ z) ⟫
-- --             )
-- --           )
-- --           (λ x → {!   !} )
-- -- --            ∃ᵖ-elim (λ i i∈I → {!   !}) {!   !}
-- --           )
--       )
--       (∧ᵖ-intro
--         (↓ λ _ _ _ _ x₁≡x₂ → x₁≡x₂) -- injective
--         (∀ᵖ-intro (λ x x∈X → ∃ᵖ-intro reflᵉ))) -- surjective

-- -- U x != x ∈ U ∧ᵖ (singelton ((id X) x) ≡ᵖ singelton y) of type Set
