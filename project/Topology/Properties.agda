------------------------------------------------------------------------
-- Project: General Topology
--
-- Properties
------------------------------------------------------------------------

module Topology.Properties where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Nullary
open import Topology.PowerSet
open import Topology.Core

------------------------------------------------------------------------

private
    variable
        ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

-- Property that for sets A and B there exist neigbourhood U of A such that U ∩ B is empty  
separated-from : {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
separated-from {ℓ₁ = ℓ₁} {ℓ₅ = ℓ₅} {X = X} {τ = τ} A B = 
    Σ[ U ∈ ℙ ℓ₁ X ] (topology.Open τ U × A ⊆ U × (U ∩ B ⊆ empty {k = ℓ₅} X))

-- Same as above for both A and B. Aditionaly neigbourhoods of A and B does not intersect
separated : {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
separated {ℓ₁ = ℓ₁} {ℓ₅ = ℓ₅} {X = X} {τ = τ} A B = 
    Σ[ U ∈ ℙ ℓ₁ X ] (Σ[ V ∈ ℙ ℓ₁ X ] 
        topology.Open τ U × topology.Open τ V
        × A ⊆ U × B ⊆ V × U ∩ V ⊆ empty {k = ℓ₅} X)

-- Topologically indistinguishable points
indistinguishable : {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (x : X) → (y : X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂)
indistinguishable {ℓ₁ = ℓ₁} {X = X} {τ = τ} x y = 
    (∀ (U : ℙ ℓ₁ X) → topology.Open τ U → x ∈ U → y ∈ U)
    × (∀ (V : ℙ ℓ₁ X) → topology.Open τ V → y ∈ V → x ∈ V)

------------------------------------------------------------------------
-- Separation axioms

-- Kolmogorov space
is-T₀ : (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂)
is-T₀ X τ = ∀ (x y : X) 
    → indistinguishable {τ = τ} x y
    → x ≡ y

-- Symetric space
is-R₀ : (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-R₀ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ indistinguishable {τ = τ} x y
    → separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y) × 
    separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton y) (singleton x)

-- Frechet space
is-T₁ : (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-T₁ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ singleton x ≡ singleton y
    → separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y) × 
    separated-from {ℓ₅ = ℓ₃} {τ = τ} (singleton y) (singleton x)

-- Preregular space
is-R₁ : (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-R₁ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ indistinguishable {τ = τ} x y
    → separated {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y)

-- Hausdorff space
is-T₂ : (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (lsuc ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-T₂ {ℓ₃ = ℓ₃} X τ = ∀ (x y : X) 
    → ¬ singleton x ≡ singleton y
    → separated {ℓ₅ = ℓ₃} {τ = τ} (singleton x) (singleton y)

-- Regular space - There exists disjoint neigbourhoods for a closed set Y ⊆ X and a point x ∈ X with x ∉ Y.
is-regular : (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
is-regular {ℓ₁ = ℓ₁} {ℓ₃ = ℓ₃} X τ = ∀ (x : X) → (Y : ℙ ℓ₁ X) 
    → topology.Open τ (Y ᶜ) → x ∉ Y
    → separated {ℓ₅ = ℓ₃} {τ = τ} (singleton x) Y

------------------------------------------------------------------------

∩-U-0-∩-0 : {X : Set ℓ₀} {A : ℙ ℓ₁ X} {B : ℙ ℓ₂ X} {U : ℙ ℓ₃ X} 
    → (B⊆U : B ⊆ U) → (A∩U=0 : A ∩ U ⊆ empty {k = ℓ₄} X) 
    → A ∩ B ⊆ empty {k = ℓ₄} X
∩-U-0-∩-0 {X = X} {A = A} {U = U} B⊆U A∩U=0 = λ x x∈A∩B 
    → A∩U=0 x (∈-both-∈-∩ {A = X} {x = x} {U = A} {V = U}
        (proj₁ x∈A∩B) (∈-⊆-∈ (proj₂ x∈A∩B) B⊆U))

separated-separated-from₁ : {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) 
    → (ABsep : separated {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} A B) 
    → separated-from {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} A B
separated-separated-from₁ A B (U , V , OpenU , OpenV , A⊆U , B⊆V , U∩V⊆0) = 
    U , OpenU , A⊆U , ∩-U-0-∩-0 B⊆V U∩V⊆0

separated-separated-from₂ : {X : Set ℓ₀} {τ : topology ℓ₁ ℓ₂ X} 
    → (A : ℙ ℓ₃ X) → (B : ℙ ℓ₄ X) 
    → (ABsep : separated {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} A B) 
    → separated-from {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₅ = ℓ₅} {τ = τ} B A
separated-separated-from₂ {ℓ₅ = ℓ₅} {X = X} A B (U , V , OpenU , OpenV , A⊆U , B⊆V , U∩V⊆0) = 
    V , OpenV , B⊆V , ∩-U-0-∩-0 A⊆U (∩-⊆-symetric {A = X} {U = U} 
            {V = V} {B = empty {k = ℓ₅} X}
            U∩V⊆0)

R₁-is-R₀ : (X : Set ℓ₀) → (τ : topology ℓ₁ ℓ₂ X) → (isR₁ : is-R₁ {ℓ₃ = ℓ₃} X τ) 
    → is-R₀ {ℓ₃ = ℓ₃} X τ
R₁-is-R₀ X τ isR₁ = λ x y disting → 
    separated-separated-from₁ {τ = τ} (singleton x) (singleton y) (isR₁ x y disting) , 
    separated-separated-from₂ {τ = τ} (singleton x) (singleton y) (isR₁ x y disting)
