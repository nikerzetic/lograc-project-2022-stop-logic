------------------------------------------------------------------------
-- Project ???
--
-- Logic, subsets and power sets
------------------------------------------------------------------------

{-# OPTIONS --prop #-}

module Topology.Logic where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Bool

infix 0 ⟪_⟫

-- The collapsing function (also known as "resizing")
postulate ⟪_⟫ : {ℓ : Level} (p : Prop ℓ) → Prop

-- Conversions to and from the collapsed propositions
postulate ↓ : {ℓ : Level} {p : Prop ℓ} → p → ⟪ p ⟫
postulate ↑ : {ℓ : Level} {p : Prop ℓ} → ⟪ p ⟫ → p

-- Propositional extensionality
postulate prop-ext : {p q : Prop} → (p → q) → (q → p) → p ≡ q

------------------------------------------------------------------------
-- Logic

-- False
data ⊥ᵖ : Prop where

⊥ᵖ-elim : {ℓ : Level} {p : Prop ℓ} → ⊥ᵖ → p
⊥ᵖ-elim ()

-- True
record ⊤ᵖ : Prop where
    constructor ⊤ᵖ-intro

-- Conjunction
data _∧ᵖ_ : Prop → Prop → Prop where
    ∧ᵖ-intro : {p q : Prop} → p → q → p ∧ᵖ q


-- Disjunction
data _∨ᵖ_ : Prop → Prop → Prop where
    ∨ᵖ-intro₁ : {p q : Prop} → p → p ∨ᵖ q
    ∨ᵖ-intro₂ : {p q : Prop} → q → p ∨ᵖ q

∧ᵖ-elim₁ : {p q : Prop} → p ∧ᵖ q → p
∧ᵖ-elim₁ (∧ᵖ-intro a b) = a

∧ᵖ-elim₂ : {p q : Prop} → p ∧ᵖ q → q
∧ᵖ-elim₂ (∧ᵖ-intro a b) = b

-- ∨ᵖ-elim : {p q : Prop} →  p ∨ᵖ q → ?
    
-- Universal quantifier
∀ᵖ : {ℓ : Level} {A : Set ℓ} → (A → Prop) → Prop
∀ᵖ p = ⟪ (∀ x → p x) ⟫

∀ᵖ-intro : {ℓ : Level} {A : Set ℓ} {u : A → Prop} → ((x : A) → u x) → ∀ᵖ u
∀ᵖ-intro = ↓

∀ᵖ-elim :  {ℓ : Level} {A : Set ℓ} {u : A → Prop} → ∀ᵖ u → (x : A) → u x
∀ᵖ-elim = ↑

-- Existential quantifier
data ∃ {ℓ : Level} {A : Set ℓ} : (A → Prop) → Prop ℓ where
    ∃-intro : ∀ {u : A → Prop} {a : A} → u a → ∃ u

∃ᵖ : {ℓ : Level} {A : Set ℓ} → (A → Prop) → Prop
∃ᵖ p = ⟪ (∃ p) ⟫

∃ᵖ-elim : {ℓ : Level} {A : Set ℓ} {u : A → Prop} {q : Prop} → (∀ a → u a → q) → ∃ᵖ u → q
∃ᵖ-elim p r with ↑ r
... | ∃-intro x = p _ x

∃ᵖ-intro : {ℓ : Level} {A : Set ℓ} {u : A → Prop} {a : A} → u a → ∃ᵖ u
∃ᵖ-intro p = ↓ (∃-intro p)
