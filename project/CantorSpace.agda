------------------------------------------------------------------------
-- Project: General Topology
--
-- Cantor space
------------------------------------------------------------------------

module CantorSpace where

open import Agda.Primitive
open import Axiom.Extensionality.Propositional renaming (Extensionality to PropExt)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum
open import Function.Construct.Composition
open import Topology.PowerSet
open import Topology.Core
open import Topology.Properties

------------------------------------------------------------------------

infix 4 _⊏_
infix 4 _⊑'_

private
    variable
        ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------

-- The relation of "is head/heads" for lists
data _⊑'_ : Rel (List Bool) lzero where 
    []⊑' : ∀ {l}                            → [] ⊑' l
    ∷⊑'  : ∀ {x l₁ l₂} (l₁⊑'l₂ : l₁ ⊑' l₂) → (x ∷ l₁) ⊑' (x ∷ l₂)

-- Shifts the series right by one
shift : (ℕ → Bool) → (ℕ → Bool)
shift a = λ n → a (suc n)

-- The relation of "is head/heads" for a list and a series
data _⊏_ : REL (List Bool) (ℕ → Bool) lzero where
    []⊏ : ∀ {a}                               → [] ⊏ a
    ∷⊏  : ∀ {a} {l : List Bool} → l ⊏ shift a → a 0 ∷ l ⊏ a

    -- Implicitnost l ???

-- Transitivity for "heads" relations
⊑'-⊏ : ∀ {l₁ l₂ a} → (l₁⊑'l₂ : l₁ ⊑' l₂) → (l₂⊏a : l₂ ⊏ a) → l₁ ⊏ a
⊑'-⊏ []⊑' l₂⊏a = []⊏
⊑'-⊏ {l₁} {l₂} (∷⊑' l₁⊑'l₂) (∷⊏ l₂⊏a) = ∷⊏ (⊑'-⊏ l₁⊑'l₂ l₂⊏a)

------------------------------------------------------------------------

-- The basis of the Cantor space topology
B : List Bool → ℙ lzero (ℕ → Bool)
B l a = l ⊏ a

-- Topology on the Cantor space
τᶜ : topology lzero lzero (ℕ → Bool)
τᶜ = base B (λ a →  [] , []⊏) 
        (λ x∈Bi x∈Bj → ∈-∈-list x∈Bi x∈Bj , 
            ⊑'-⊎-⊑'-∈ x∈Bi x∈Bj , 
            ⊑'-⊎-⊑'-⊆   x∈Bi x∈Bj)

    where

        B-[]-=-UB : ∀ {a} → a ∈ union B → a ∈ B []
        B-[]-=-UB {a} a∈UB = []⊏

        ⊑'-B-⊆ : ∀ { l₁ l₂} (l₁⊑'l₂ : l₁ ⊑' l₂) → B l₂ ⊆ B l₁
        ⊑'-B-⊆ l₁⊑'l₂ = λ a a∈Bl₂ → ⊑'-⊏ l₁⊑'l₂ a∈Bl₂

        ∷-⊑'-⊎-⊑' : ∀ {l₁ l₂} (x : Bool) 
            → (l₂⊑'l₁⊎l₁⊑'l₂ : l₂ ⊑' l₁ ⊎ l₁ ⊑' l₂) 
            → x ∷ l₂ ⊑' x ∷ l₁ ⊎ x ∷ l₁ ⊑' x ∷ l₂
        ∷-⊑'-⊎-⊑' x (inj₁ l₂⊑'l₁) = inj₁ (∷⊑' {x = x} l₂⊑'l₁)
        ∷-⊑'-⊎-⊑' x (inj₂ l₁⊑'l₂) = inj₂ (∷⊑' {x = x} l₁⊑'l₂)

        ⊏-⊏-⊑'-⊎-⊑' : ∀ {l₁ l₂ a} → (l₁⊏a : l₁ ⊏ a) → (l₂⊏a : l₂ ⊏ a) 
            → l₂ ⊑' l₁ ⊎ l₁ ⊑' l₂
        ⊏-⊏-⊑'-⊎-⊑' l₁⊏a []⊏ = inj₁ []⊑'
        ⊏-⊏-⊑'-⊎-⊑' []⊏ (∷⊏ l₂⊏a) = inj₂ []⊑'
        ⊏-⊏-⊑'-⊎-⊑' {a = a} (∷⊏ l₁⊏a) (∷⊏ l₂⊏a) = 
            ∷-⊑'-⊎-⊑' (a 0) (⊏-⊏-⊑'-⊎-⊑' l₁⊏a l₂⊏a)

        ⊑'-⊎-⊑'-list : ∀ {l₁ l₂}
            → (l₂⊑'l₁⊎l₁⊑'l₂ : l₂ ⊑' l₁ ⊎ l₁ ⊑' l₂) → List Bool
        ⊑'-⊎-⊑'-list {l₁ = l₁} (inj₁ _) = l₁
        ⊑'-⊎-⊑'-list {l₂ = l₂} (inj₂ _) = l₂

        ∈-∈-list : ∀ {l₁ l₂ a} → (a∈Bl₁ : a ∈ B l₁) → (a∈Bl₂ : a ∈ B l₂)
            → List Bool
        ∈-∈-list a∈Bl₁ a∈Bl₂ = ⊑'-⊎-⊑'-list (⊏-⊏-⊑'-⊎-⊑' a∈Bl₁ a∈Bl₂)
        
        ⊑'-⊎-⊑'-∈ : ∀ {l₁ l₂ a} 
            → (a∈Bl₁ : a ∈ B l₁) → (a∈Bl₂ : a ∈ B l₂)
            → a ∈ B (∈-∈-list a∈Bl₁ a∈Bl₂)
        ⊑'-⊎-⊑'-∈ {l₁ = l₁} {l₂ = l₂} a∈Bl₁ a∈Bl₂ with ⊏-⊏-⊑'-⊎-⊑' a∈Bl₁ a∈Bl₂
        ... | inj₁ _ = a∈Bl₁
        ... | inj₂ _ = a∈Bl₂

        ⊑'-⊎-⊑'-⊆ : ∀ {l₁ l₂ a} 
            → (a∈Bl₁ : a ∈ B l₁) → (a∈Bl₂ : a ∈ B l₂)
            → B (∈-∈-list a∈Bl₁ a∈Bl₂) ⊆ B l₁ ∩ B l₂
        ⊑'-⊎-⊑'-⊆ {l₁ = l₁} {l₂ = l₂} a∈Bl₁ a∈Bl₂ with ⊏-⊏-⊑'-⊎-⊑' a∈Bl₁ a∈Bl₂
        ... | inj₁ l₂⊑'l₁ = λ x x∈Bl₁ → x∈Bl₁ , ⊑'-⊏ l₂⊑'l₁ x∈Bl₁
        ... | inj₂ l₁⊑'l₂ = λ x x∈Bl₂ → ⊑'-⊏ l₁⊑'l₂ x∈Bl₂ , x∈Bl₂

------------------------------------------------------------------------

postulate
  fun-ext : ∀ {a b} → PropExt a b

-- Series' head of length n
_↾_ : (ℕ → Bool) → ℕ → List Bool
a ↾ zero = a 0 ∷ []
a ↾ suc n = a 0 ∷ ((shift a) ↾ n)

-- Series' head heads the series
↾-⊏ : ∀ {a n} → a ↾ n ⊏ a
↾-⊏ {n = zero} = ∷⊏ []⊏
↾-⊏ {a = a} {n = suc n} = ∷⊏ (↾-⊏ {a = shift a} {n = n})

first-≡ : ∀ {x xs a} → x ∷ xs ⊏ a → x ≡ a 0
first-≡ (∷⊏ x∷xs⊏a) = refl

-- Head equality implies pointwise equality
-- ↾-⊏-≡ : ∀ {a b n} → a ↾ (suc n) ⊏ b → a n ≡ b n
↾-⊏-≡ : ∀ {a b n} → a ↾ n ⊏ b → a n ≡ b n
↾-⊏-≡ {n = zero} a↾⊏b = first-≡ a↾⊏b
↾-⊏-≡ {a} {b} {n = suc n} a↾⊏b = {!    !}

-- Proof that the Cantor space is T₀
ℂ-is-T₀ : is-T₀ (ℕ → Bool) τᶜ
ℂ-is-T₀ = λ a b indisting-a-b 
    → fun-ext (λ n → pointwise-equality a b n 
        ((proj₁ indisting-a-b) (B (a ↾ n)) 
            (↾-open {a = a} {n = n}) 
            (↾-⊏ {a = a} {n = n})))
            -- ??? To bi se najbrz dalo lepse napisati - z redefinicijo zgornjih funkcij (↾-open ↾-⊏)

    where 
        ↾-open : ∀ {a n} → topology.Open τᶜ (B (a ↾ n))
        ↾-open {a} {n} = λ x∈B↾ 
            → (a ↾ n) , 
                (λ y y∈B↾ → y∈B↾) , 
                x∈B↾

        pointwise-equality : (x : ℕ → Bool) → (y : ℕ → Bool) → (n : ℕ) 
            → y ∈ B (x ↾ n) -- x ↑ n ⊏ y
            → x n ≡ y n
        pointwise-equality x y n y∈B↾ = ↾-⊏-≡ {a = x} {b = y} {n = n} y∈B↾

