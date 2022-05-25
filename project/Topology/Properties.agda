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
separated-from : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
separated-from {ℓ₁ = ℓ₁} {ℓ₅ = ℓ₅} {X = X} {τ = τ} A B = 
    Σ[ U ∈ ℙ ℓ₁ X ] (topology.Open τ U × A ⊆ U × (U ∩ B ⊆ empty {k = ℓ₅} X))

-- Strictly separated sets
separated : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
separated {ℓ₁ = ℓ₁} {ℓ₅ = ℓ₅} {X = X} {τ = τ} A B = 
    Σ[ U ∈ ℙ ℓ₁ X ] (Σ[ V ∈ ℙ ℓ₁ X ] 
        topology.Open τ U × topology.Open τ V
        × A ⊆ U × B ⊆ V × U ∩ V ⊆ empty {k = ℓ₅} X)

-- Topologically indistinguishable points
indistinguishable : {ℓ₀ ℓ₁ ℓ₂ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (x : X) → (y : X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂)
indistinguishable {ℓ₁ = ℓ₁} {X = X} {τ = τ} x y = 
    ∀ (U : ℙ ℓ₁ X) → topology.Open τ U → x ∈ U → y ∈ U 
    × ∀ (V : ℙ ℓ₁ X) → topology.Open τ V → y ∈ V → x ∈ V

------------------------------------------------------------------------
-- Separation axioms

-- Kolmogorov space
is-T₀ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂)
is-T₀ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ singleton x ≡ singleton y
    → ¬ indistinguishable {τ = τ} x y

-- Symetric space
is-R₀ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-R₀ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ indistinguishable {τ = τ} x y
    → separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y) × 
    separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton y) (singleton x)

-- Frechet space
is-T₁ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-T₁ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ singleton x ≡ singleton y
    → separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y) × 
    separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton y) (singleton x)

-- Preregular space
is-R₁ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-R₁ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ indistinguishable {τ = τ} x y
    → separated {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y)

-- Hausdorff space
is-T₂ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-T₂ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ singleton x ≡ singleton y
    → separated {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y)

-- Regular space
is-regular : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-regular {ℓ₁ = ℓ₁} {ℓ₃ = ℓ₃} X τ = ∀ (x : X) → (Y : ℙ ℓ₁ X) 
    → topology.Open τ (Y ᶜ) → x ∉ Y
    → separated {ℓ₅ = ℓ₃} {τ = τ} (singleton x) Y

------------------------------------------------------------------------

∩-U-0-∩-0 : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {X : Set ℓ₀} {A : ℙ ℓ₁ X} {B : ℙ ℓ₂ X} {U : ℙ ℓ₃ X} 
    → (B⊆U : B ⊆ U) → (A∩U=0 : A ∩ U ⊆ empty {k = ℓ₄} X) 
    → A ∩ B ⊆ empty {k = ℓ₄} X
∩-U-0-∩-0 {X = X} {A = A} {U = U} B⊆U A∩U=0 = λ x x∈A∩B 
    → A∩U=0 x (∈-both-∈-∩ {A = X} {x = x} {U = A} {V = U}
        (proj₁ x∈A∩B) (∈-⊆-∈ (proj₂ x∈A∩B) B⊆U))

separated-separated-from₁ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) 
    → (ABsep : separated {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} A B) 
    → separated-from {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} A B
separated-separated-from₁ A B ABsep = 
    proj₁ ABsep , 
    proj₁ (proj₂ (proj₂ ABsep)) , 
    proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ABsep)))) , 
    ∩-U-0-∩-0 (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ABsep)))))) 
        (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ABsep))))))

separated-separated-from₂ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) 
    → (ABsep : separated {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} A B) 
    → separated-from {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} B A
separated-separated-from₂ {ℓ₄ = ℓ₄} {ℓ₅ = ℓ₅} {X = X} A B ABsep = 
    proj₁ (proj₂ ABsep) , 
    proj₁ (proj₂ (proj₂ (proj₂ ABsep))) , 
    proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ABsep))))) , 
    ∩-U-0-∩-0 (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ABsep))))) 
        (∩-⊆-symetric {A = X} {U = proj₁ ABsep} 
            {V = proj₁ (proj₂ ABsep)} {B = empty {k = ℓ₅} X}
            (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ABsep)))))))

-- To je tako horrible - I hate myself. Zato obstajajo record tipi

R₁-is-R₀ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level}
    → (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → (isR₁ : is-R₁ {ℓ₃ = ℓ₃} X τ) 
    → is-R₀ {ℓ₃ = ℓ₃} X τ
R₁-is-R₀ X τ isR₁ = λ x y disting → 
    separated-separated-from₁ {τ = τ} (singleton x) (singleton y) (isR₁ x y disting) , 
    separated-separated-from₂ {τ = τ} (singleton x) (singleton y) (isR₁ x y disting)
