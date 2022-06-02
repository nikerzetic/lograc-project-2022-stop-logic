------------------------------------------------------------------------
-- Project: General Topology
--
-- Cantor space
------------------------------------------------------------------------

module CantorSpace where

open import Agda.Primitive
open import Relation.Binary
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum
open import Function.Construct.Composition
open import Topology.PowerSet
open import Topology.Core

------------------------------------------------------------------------

infix 4 _⊏_
infix 4 _⊑'_

------------------------------------------------------------------------

variable
    ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------

-- data ℂ : ℕ → Bool 

-- 2^_ : Set → Set
-- 2^ A = A → Bool

data _⊑'_ : Rel (List Bool) lzero where 
    []⊑' : ∀ {l}                            → [] ⊑' l
    ∷⊑'  : ∀ {x l₁ l₂} (l₁⊑'l₂ : l₁ ⊑' l₂) → (x ∷ l₁) ⊑' (x ∷ l₂)

shift : (ℕ → Bool) → (ℕ → Bool)
shift a = λ n → a (suc n)

data _⊏_ : REL (List Bool) (ℕ → Bool) lzero where
    []⊏ : ∀ {a} → [] ⊏ a
    ∷⊏  : ∀ {a} {l : List Bool} → l ⊏ shift a → a 0 ∷ l ⊏ a

    -- Implicitnost l ???

⊑'-⊏ : ∀ {l₁ l₂ a} → (l₁⊑'l₂ : l₁ ⊑' l₂) → (l₂⊏a : l₂ ⊏ a) → l₁ ⊏ a
⊑'-⊏ []⊑' l₂⊏a = []⊏
⊑'-⊏ {l₁} {l₂} (∷⊑' l₁⊑'l₂) (∷⊏ l₂⊏a) = ∷⊏ (⊑'-⊏ l₁⊑'l₂ l₂⊏a)

------------------------------------------------------------------------

B : List Bool → ℙ lzero (ℕ → Bool)
B l a = l ⊏ a

-- Topology on the Cantor space
τᶜ : topology lzero {!   !} (ℕ → Bool)
τᶜ = base B (λ a →  [] , []⊏) 
        (λ x∈Bi x∈Bj → ∈-∈-list x∈Bi x∈Bj , 
            ⊑'-⊎-⊑'-∈ x∈Bi x∈Bj , 
            {!   !})

    where
        B-[]-=-UB : ∀ {a} → a ∈ union B → a ∈ B []
        B-[]-=-UB {a} a∈UB = []⊏

        l₁⊑'l₂-Bl₂⊆Bl₁ : ∀ { l₁ l₂} (l₁⊑'l₂ : l₁ ⊑' l₂) → B l₂ ⊆ B l₁
        l₁⊑'l₂-Bl₂⊆Bl₁ l₁⊑'l₂ = λ a a∈Bl₂ → ⊑'-⊏ l₁⊑'l₂ a∈Bl₂

        ∷-⊑'-⊎-⊑' : ∀ {l₁ l₂} (x : Bool) 
            → (l₂⊑'l₁⊎l₁⊑'l₂ : l₂ ⊑' l₁ ⊎ l₁ ⊑' l₂) 
            → x ∷ l₂ ⊑' x ∷ l₁ ⊎ x ∷ l₁ ⊑' x ∷ l₂
        ∷-⊑'-⊎-⊑' x (inj₁ l₂⊑'l₁) = inj₁ (∷⊑' {x = x} l₂⊑'l₁)
        ∷-⊑'-⊎-⊑' x (inj₂ l₁⊑'l₂) = inj₂ (∷⊑' {x = x} l₁⊑'l₂)

        ⊏-⊏-⊑'-⊑' : ∀ {l₁ l₂ a} → (l₁⊏a : l₁ ⊏ a) → (l₂⊏a : l₂ ⊏ a) 
            → l₂ ⊑' l₁ ⊎ l₁ ⊑' l₂
        ⊏-⊏-⊑'-⊑' l₁⊏a []⊏ = inj₁ []⊑'
        ⊏-⊏-⊑'-⊑' []⊏ (∷⊏ l₂⊏a) = inj₂ []⊑'
        ⊏-⊏-⊑'-⊑' {a = a} (∷⊏ l₁⊏a) (∷⊏ l₂⊏a) = 
            ∷-⊑'-⊎-⊑' (a 0) (⊏-⊏-⊑'-⊑' l₁⊏a l₂⊏a)

        ⊑'-⊎-⊑'-list : ∀ {l₁ l₂}
            → (l₂⊑'l₁⊎l₁⊑'l₂ : l₂ ⊑' l₁ ⊎ l₁ ⊑' l₂) → List Bool
        ⊑'-⊎-⊑'-list {l₂ = l₂} (inj₁ _) = l₂
        ⊑'-⊎-⊑'-list {l₁ = l₁} (inj₂ _) = l₁

        ∈-∈-list : ∀ {l₁ l₂ a} → (a∈Bl₁ : a ∈ B l₁) → (a∈Bl₂ : a ∈ B l₂)
            → List Bool
        ∈-∈-list a∈Bl₁ a∈Bl₂ = ⊑'-⊎-⊑'-list (⊏-⊏-⊑'-⊑' a∈Bl₁ a∈Bl₂)
        
        ⊑'-⊎-⊑'-∈ : ∀ {l₁ l₂ a} 
            → (a∈Bl₁ : a ∈ B l₁) → (a∈Bl₂ : a ∈ B l₂)
            → a ∈ B (∈-∈-list a∈Bl₁ a∈Bl₂)
        ⊑'-⊎-⊑'-∈ {l₁ = l₁} {l₂ = l₂} a∈Bl₁ a∈Bl₂ with ⊏-⊏-⊑'-⊑' a∈Bl₁ a∈Bl₂
        ... | inj₁ _ = a∈Bl₂
        ... | inj₂ _ = a∈Bl₁

