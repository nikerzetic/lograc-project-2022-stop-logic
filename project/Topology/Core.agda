------------------------------------------------------------------------
-- Project ???
--
-- Sierpinski space
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}


module Topology.Core where

open import Agda.Primitive
open import Topology.PowerSet
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Unit
open import Data.Empty

------------------------------------------------------------------------
-- Topology on a set X
record topology {ℓ} (k m : Level) (X : Set ℓ) : Setω₁ where
    field
        Open : ℙ k X → Set m -- the open subsets of X
        ∅-open : Open (empty X)
        full-open : Open (full X)
        ∩-open : ∀ U V → Open U → Open V → Open (U ∩ V)
        union-open : ∀ {I : Set k} (S : I → ℙ k X) → (∀ i → Open (S i)) → Open (union S)

open topology public

data ⊤ℓ {ℓ : Level} : Set ℓ where 
    ⊤ℓ-intro : ⊤ℓ

discrete-topology : {ℓ k : Level} (X : Set ℓ) → topology k lzero X
discrete-topology X =
    record
        { Open = λ _ → ⊤ℓ
        ; ∅-open = ⊤ℓ-intro
        ; full-open = ⊤ℓ-intro
        ; ∩-open = λ _ _ _ _ → ⊤ℓ-intro
        ; union-open = λ _ _ → ⊤ℓ-intro
        }

-- Trivial topology
indiscrete-topology : {ℓ k : Level} (X : Set ℓ) → topology k (ℓ ⊔ k) X
indiscrete-topology X =
    record
        { Open = λ U → ∀ x → U x → ∀ y → U y
        ; ∅-open = λ { p () y}
        ; full-open = λ p x y → full-intro
        ; ∩-open = λ U V OpenU OpenV x UVx z → (OpenU x (∩-⊆-left U V x UVx) z) ,
                                              (OpenV x (∩-⊆-right U V x UVx) z)
        ; union-open = 
            λ { S Si-open x (i , xSi) y → i , Si-open i x xSi y }        
        }

-- The topology generated by a family B of subsets closed under binary intersection
base : {ℓ k j : Level} {X : Set ℓ} {I : Set k}
    → (B : I → (ℙ j X))
    → ((x : X) → x ∈ union B)
    → (∀ {i j x} → x ∈ B i → x ∈ B j → Σ[ k ∈ I ] (x ∈ B k) × (B k ⊆ B i ∩ B j))
    → topology j (ℓ ⊔ k ⊔ j) X
base {ℓ = ℓ} {k = k} {j = j} {X = X} {I = I} B Bcovers Bbase =
  record
    { Open = Open'
    ; ∅-open = λ { () }
    ; full-open = λ {x} _ → (proj₁ (Bcovers x)) , ((λ y _ → full-intro) , proj₂ (Bcovers x))
    ; ∩-open = ∩-open'
    ; union-open = union-open'
    }
  where
    Open' : (U : X → Set j) → Set (ℓ ⊔ k ⊔ j)
    Open' = λ U → ∀ {x} → x ∈ U → Σ[ i ∈ I ] (B i ⊆ U) × x ∈ B i

    index-of : {x : X} {U : ℙ j X} → x ∈ U → Open' U → I
    index-of x∈U OpenU = proj₁ (OpenU x∈U)

    B-⊆ : {x : X} {U : ℙ j X} (x∈U : x ∈ U) (OpenU : Open' U) → B(index-of x∈U OpenU) ⊆ U
    B-⊆ x∈U OpenU = λ y → proj₁ (proj₂ (OpenU x∈U)) y

    ∈-B : {x : X} {U : ℙ j X} (x∈U : x ∈ U) (OpenU : Open' U) → x ∈ B(index-of x∈U OpenU)
    ∈-B x∈U OpenU = proj₂ (proj₂ (OpenU x∈U))

    ∩-index-of : ∀ {i j x} → x ∈ B i → x ∈ B j → I
    ∩-index-of x∈Bi x∈Bj = proj₁ (Bbase x∈Bi x∈Bj)

    B-⊆-∩ : ∀ {i j x} → (x∈Bi : x ∈ B i) → (x∈Bj : x ∈ B j) → B (∩-index-of x∈Bi x∈Bj) ⊆ B i ∩ B j
    B-⊆-∩ x∈Bi x∈Bj = proj₂ (proj₂ (Bbase x∈Bi x∈Bj))

    B-∈-B : ∀ {i j x} → (x∈Bi : x ∈ B i) → (x∈Bj : x ∈ B j) → x ∈ B (∩-index-of x∈Bi x∈Bj)
    B-∈-B x∈Bi x∈Bj = proj₁ (proj₂ (Bbase x∈Bi x∈Bj))

    ∩-open' : (U V : ℙ j X) → Open' U → Open' V → Open' (U ∩ V)
    ∩-open' U V OpenU OpenV (x∈U , x∈V) =  
        ∩-index-of (∈-B x∈U OpenU) (∈-B x∈V OpenV) , 
            ((λ y y∈B → 
                B-⊆ x∈U OpenU y 
                    (∩-⊆-left (B (index-of x∈U OpenU)) (B (index-of x∈V OpenV)) y 
                        ((B-⊆-∩ (∈-B x∈U OpenU) (∈-B x∈V OpenV)) y y∈B )) , 
                B-⊆ x∈V OpenV y 
                    (∩-⊆-right (B (index-of x∈U OpenU)) (B (index-of x∈V OpenV)) y 
                        ((B-⊆-∩ (∈-B x∈U OpenU) (∈-B x∈V OpenV)) y y∈B ))) , 
            B-∈-B (∈-B x∈U OpenU) (∈-B x∈V OpenV))

    union-open' : {J : Set j} (S : J → ℙ j X) → ((m : J) → Open' (S m)) → Open' (union S)
    union-open' S OpenSm x∈US = 
        index-of (∈-union-∈-member {S = S} x∈US) (OpenSm (union-index-of {S = S} x∈US)) ,
            ((λ x x∈Bi → 
                ∈-member-∈-union {S = S} (∈-⊆-∈ x∈Bi (B-⊆ 
                    (∈-union-∈-member {S = S} x∈US) (OpenSm (union-index-of {S = S} x∈US))))) , 
            ∈-B (∈-union-∈-member {S = S} x∈US) (OpenSm (union-index-of {S = S} x∈US)))

