------------------------------------------------------------------------
-- Project ???
--
-- Subsets and power sets
------------------------------------------------------------------------

module Topology.PowerSet where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Product

------------------------------------------------------------------------

infix 4 _∩_
infix 3 _∈_
infix 3 _⊆_

------------------------------------------------------------------------

-- Predicative “powerset”
ℙ : {ℓ : Level} (k : Level) → Set ℓ → Set (ℓ ⊔ lsuc k)
ℙ k A = A → Set k

_∈_ : {k ℓ : Level} {A : Set ℓ} → A → ℙ k A → Set k
x ∈ S = S x

data 𝟘 {ℓ : Level} : Set ℓ where

-- The empty subset
empty : {ℓ k : Level} (A : Set ℓ) → ℙ k A
empty _ _ = 𝟘

data 𝟙 {ℓ : Level} : Set ℓ where
  𝟙-intro : 𝟙

-- The full subset
full : {ℓ k : Level} (A : Set ℓ) → ℙ k A
full _ _ = 𝟙

-- Subset relation
_⊆_ : {ℓ k m : Level} {A : Set ℓ} → ℙ k A → ℙ m A → Set (ℓ ⊔ k ⊔ m)
S ⊆ T = ∀ x → S x → T x

-- Subset extensionality
postulate ⊆-⊇-≡ : {ℓ k : Level} {A : Set ℓ} (S T : ℙ k A) → S ⊆ T → T ⊆ S → S ≡ T

-- Union of a family
union : {ℓ k j : Level} {I : Set ℓ} {A : Set k} → (I → ℙ j A) → ℙ (ℓ ⊔ j) A
union {I = I} S x = Σ[ i ∈ I ] S i x

-- Binary intersection
_∩_ : {ℓ k m : Level} {A : Set ℓ} → ℙ k A → ℙ m A → ℙ (k ⊔ m) A
U ∩ V = λ x → U x × V x

∩-⊆-left : {ℓ k m : Level} {A : Set ℓ} (U : ℙ k A) (V : ℙ m A) → U ∩ V ⊆ U
∩-⊆-left U V x (Ux , _) = Ux

∩-⊆-right : {ℓ k m : Level} {A : Set ℓ} (U : ℙ k A) (V : ℙ m A) → U ∩ V ⊆ V
∩-⊆-right U V x (_ , Vx) = Vx
