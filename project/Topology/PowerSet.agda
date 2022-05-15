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

data ⊥ℓ {ℓ : Level} : Set ℓ where 

data ⊤ℓ {ℓ : Level} : Set ℓ where
  ⊤ℓ-intro : ⊤ℓ

-- The empty subset
data empty {ℓ k : Level} (A : Set ℓ) (x : A) : Set k where


-- The full subset
data full {ℓ k : Level} (A : Set ℓ) (x : A) : Set k where
  full-intro : full A x

-- Subset relation
_⊆_ : {ℓ k m : Level} {A : Set ℓ} → ℙ k A → ℙ m A → Set (ℓ ⊔ k ⊔ m)
S ⊆ T = ∀ x → S x → T x

-- Subset extensionality
postulate ⊆-⊇-≡ : {ℓ k : Level} {A : Set ℓ} (S T : ℙ k A) → S ⊆ T → T ⊆ S → S ≡ T

-- Union of a family
union : {ℓ k j : Level} {I : Set ℓ} {A : Set k} → (I → ℙ j A) → ℙ (ℓ ⊔ j) A
union {I = I} S x = Σ[ i ∈ I ] S i x

union-index-of : {ℓ k j : Level} {I : Set ℓ} {A : Set k} {S : I → ℙ j A} {x : A} 
  → (x∈US : x ∈ union S) → I
union-index-of x∈US = proj₁ x∈US

-- Binary intersection
_∩_ : {ℓ k m : Level} {A : Set ℓ} → ℙ k A → ℙ m A → ℙ (k ⊔ m) A
U ∩ V = λ x → U x × V x

∩-⊆-left : {ℓ k m : Level} {A : Set ℓ} (U : ℙ k A) (V : ℙ m A) → U ∩ V ⊆ U
∩-⊆-left U V x (Ux , _) = Ux

∩-⊆-right : {ℓ k m : Level} {A : Set ℓ} (U : ℙ k A) (V : ℙ m A) → U ∩ V ⊆ V
∩-⊆-right U V x (_ , Vx) = Vx
