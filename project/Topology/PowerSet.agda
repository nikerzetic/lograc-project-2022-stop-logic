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
open import Relation.Nullary

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

_∉_ : {ℓ k : Level} {A : Set ℓ} → A → ℙ k A → Set k
x ∉ S = ¬ (S x)

-- The empty subset
<<<<<<< HEAD
data empty {ℓ k : Level} (A : Set ℓ) (x : A) : Set k where

-- The full subset
data full {ℓ k : Level} (A : Set ℓ) (x : A) : Set k where
  full-intro : full A x

-- The singelton 
singleton : {ℓ : Level} {A : Set ℓ} (* : A) → ℙ ℓ A
singleton * = λ x → x ≡ *
=======
empty : {ℓ : Level} (A : Set ℓ) → ℙ A
empty _ = λ _ → ⊥ᵖ

-- The full subset
full : {ℓ : Level} (A : Set ℓ) → ℙ A
full _ = λ _ → ⊤ᵖ
>>>>>>> carovNik

-- Subset relation
_⊆_ : {ℓ k m : Level} {A : Set ℓ} → ℙ k A → ℙ m A → Set (ℓ ⊔ k ⊔ m)
S ⊆ T = ∀ x → x ∈ S → x ∈ T

-- Complement
_ᶜ : {ℓ k : Level} {A : Set ℓ} → ℙ k A → ℙ k A
_ᶜ S = λ x → x ∉ S

∈-⊆-∈ : {ℓ k m : Level} {A : Set ℓ} {U : ℙ k A} {V : ℙ m A} {x : A}
  → (x∈U : x ∈ U) → (U⊆V : U ⊆ V) → x ∈ V
∈-⊆-∈ {x = x} x∈U U⊆V = U⊆V x x∈U

-- Subset extensionality
postulate ⊆-⊇-≡ : {ℓ k : Level} {A : Set ℓ} (S T : ℙ k A) → S ⊆ T → T ⊆ S → S ≡ T

-- -- Family of sets
-- data family {ℓ k : Level} : ?
--     -- base :  → (I : Set ℓ) → (A : Set k) → (I → ℙ A)
--     cons : I → A → (I → ℙ A)

set : {ℓ : Level} → (A : Set ℓ) → ℙ A 
set A = λ (x : A) → ⊤ᵖ

-- Union of a family
union : {ℓ k j : Level} {I : Set ℓ} {A : Set k} → (I → ℙ j A) → ℙ (ℓ ⊔ j) A
union {I = I} S x = Σ[ i ∈ I ] x ∈ S i

-- union of subfamily of B 
unionᵇ : {ℓ k j m : Level} {X : Set ℓ} {I : Set k}
    → (B : I → ℙ j X) 
    → (J : ℙ m I)
    → ℙ (k ⊔ j ⊔ m) X
unionᵇ {I = I} B J x = Σ[ i ∈ I ] (J i × B i x)

union-index-of : {ℓ k j : Level} {I : Set ℓ} {A : Set k} {S : I → ℙ j A} {x : A} 
  → (x∈US : x ∈ union S) → I
union-index-of x∈US = proj₁ x∈US

∈-union-∈-member : {ℓ k j : Level} {I : Set ℓ} {A : Set k} {S : I → ℙ j A} {x : A} 
  → (x∈US : x ∈ union S) → x ∈ S (union-index-of {S = S} x∈US)
∈-union-∈-member x∈US = proj₂ x∈US

∈-member-∈-union : {ℓ k j : Level} {I : Set ℓ} {A : Set k} {S : I → ℙ j A} {x : A} {i : I}
  → (x∈Si : x ∈ S i) → x ∈ union S
∈-member-∈-union {i = i} x∈Si = i , x∈Si

-- Binary intersection
_∩_ : {ℓ k m : Level} {A : Set ℓ} → ℙ k A → ℙ m A → ℙ (k ⊔ m) A
U ∩ V = λ x → U x × V x

∩-⊆-left : {ℓ k m : Level} {A : Set ℓ} (U : ℙ k A) (V : ℙ m A) → U ∩ V ⊆ U
∩-⊆-left U V x (Ux , _) = Ux

∩-⊆-right : {ℓ k m : Level} {A : Set ℓ} (U : ℙ k A) (V : ℙ m A) → U ∩ V ⊆ V
∩-⊆-right U V x (_ , Vx) = Vx

∈-both-∈-∩ : {ℓ k m : Level} {A : Set ℓ} {x : A} {U : ℙ k A} {V : ℙ m A}
  → (x∈U : x ∈ U) → (x∈V : x ∈ V) → x ∈ U ∩ V
∈-both-∈-∩ x∈U x∈V = x∈U , x∈V

∩-symetric : {ℓ k m : Level} {A : Set ℓ} {U : ℙ k A} {V : ℙ m A} {x : A}
  → x ∈ U ∩ V → x ∈ V ∩ U
∩-symetric x∈U∩V = proj₂ x∈U∩V , proj₁ x∈U∩V 

∩-⊆-symetric : {ℓ k m n : Level} {A : Set ℓ} {U : ℙ k A} {V : ℙ m A} {B : ℙ n A}
  → U ∩ V ⊆ B → V ∩ U ⊆ B
∩-⊆-symetric {A = A} {U = U} {V = V} U∩V⊆B = 
  λ x x∈V∩U → (U∩V⊆B x) (∩-symetric {A = A} {U = V} {V = U} {x = x} x∈V∩U)
