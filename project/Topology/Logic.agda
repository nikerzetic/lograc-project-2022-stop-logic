-- ------------------------------------------------------------------------
-- -- Project ???
-- --
-- -- Logic, subsets and power sets
-- ------------------------------------------------------------------------

-- {-# OPTIONS --prop #-}

-- module Topology.Logic where

-- open import Agda.Primitive
-- open import Relation.Binary.PropositionalEquality
-- open import Data.Bool
-- open import Level using (Level; _⊔_; suc)

-- ------------------------------------------------------------------------

-- infix 1 ∃ᵖ
-- infixl 5 _∧ᵖ_ 
-- infixl 4 _∨ᵖ_
-- infixl 20 ¬ᵖ_
-- infix 0 ⟪_⟫

-- ------------------------------------------------------------------------

-- -- The collapsing function (also known as "resizing")
-- postulate ⟪_⟫ : {ℓ : Level} (p : Set ℓ) → Set

-- -- Conversions to and from the collapsed propositions
-- postulate ↓ : {ℓ : Level} {p : Set ℓ} → p → ⟪ p ⟫
-- postulate ↑ : {ℓ : Level} {p : Set ℓ} → ⟪ p ⟫ → p

-- -- Propositional extensionality
-- postulate prop-ext : {p q : Set} → (p → q) → (q → p) → p ≡ q

-- -- Subst for Prop
--     -- Set → Set → Prop Equality 
-- -- data _≡ₛₚ_ {a : Level} {A : Set a} (x : A) : A → Prop a where
-- --   instance reflₛₚ : x ≡ₛₚ x

-- -- REL : {a b : Level} →  Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
-- -- REL A B ℓ = A → B → Prop ℓ

-- -- Rel : {a : Level} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
-- -- Rel A ℓ = REL A A ℓ

-- -- _⟶_Respects_ : {ℓ₁ ℓ₂ ℓ₃ a b : Level} {A : Set a} {B : Set b} → (A → Prop ℓ₁) → (B → Prop ℓ₂) → REL A B ℓ₃ → Prop _
-- -- P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y

-- -- _Respects_ : {ℓ₁ ℓ₂ a : Level} {A : Set a} → (A → Prop ℓ₁) → Rel A ℓ₂ → Prop _
-- -- P Respects _∼_ = P ⟶ P Respects _∼_

-- -- Substitutiveᵖ : {a ℓ₁ : Level} {A : Set a} → Rel A ℓ₁ → (ℓ₂ : Level) → Prop _
-- -- Substitutiveᵖ {A = A} _∼_ p = (P : A → Prop p) → (P Respects _∼_)

-- -- substᵖ : {ℓ a : Level} {A : Set a} → Substitutiveᵖ {A = A} _≡ₛₚ_ ℓ
-- -- substᵖ P reflₛₚ p = p


-- ------------------------------------------------------------------------
-- -- Logic

-- -- False
-- data ⊥ᵖ : Set where

-- ⊥ᵖ-elim : {ℓ : Level} {p : Set ℓ}→ ⊥ᵖ → p
-- ⊥ᵖ-elim = λ ()

-- -- -- True
-- record ⊤ᵖ : Set where
--     constructor ⊤ᵖ-intro

-- -- -- Conjunction
-- data _∧ᵖ_ : Set → Set → Set where
--     ∧ᵖ-intro : {p q : Set} → p → q → p ∧ᵖ q

-- ∧ᵖ-elim₁ : {p q : Set} → p ∧ᵖ q → p
-- ∧ᵖ-elim₁ (∧ᵖ-intro a b) = a

-- ∧ᵖ-elim₂ : {p q : Set} → p ∧ᵖ q → q
-- ∧ᵖ-elim₂ (∧ᵖ-intro a b) = b

-- -- Negation 
-- ¬ᵖ_ : {ℓ : Level} → Set ℓ → Set ℓ
-- ¬ᵖ p = p → ⊥ᵖ

-- ¬ᵖ¬ᵖ-elim : (ℓ : Level) → Set (suc ℓ)
-- ¬ᵖ¬ᵖ-elim ℓ = {p : Set ℓ} → ¬ᵖ ¬ᵖ p → p

-- ¬ᵖ-intro : {ℓ : Level} {p q : Set ℓ}→ (p → q) → (p → ¬ᵖ q) → ¬ᵖ p
-- ¬ᵖ-intro f g x = g x (f x)

-- -- Disjunction
-- data _∨ᵖ_ : Set → Set  → Set where
--     ∨ᵖ-intro₁ : {p q : Set} → p → p ∨ᵖ q
--     ∨ᵖ-intro₂ : {p q : Set} → q → p ∨ᵖ q

-- ∨ᵖ-elim : {p q r : Set} → p ∨ᵖ q → (p → r) → (q → r) → r
-- ∨ᵖ-elim (∨ᵖ-intro₁ p) p-holds _ = p-holds p
-- ∨ᵖ-elim (∨ᵖ-intro₂ q) _ q-holds = q-holds q

-- -- Implication 
-- _⇒ᵖ_ : Set → Set → Set
-- p ⇒ᵖ q = (¬ᵖ p) ∨ᵖ q

-- -- Universal quantifier
-- ∀ᵖ : {ℓ : Level} {A : Set ℓ} → (A → Set) → Set
-- ∀ᵖ p = ⟪ (∀ x → p x) ⟫

-- ∀ᵖ-intro : {ℓ : Level} {A : Set ℓ} {u : A → Set} → ((x : A) → u x) → ∀ᵖ u
-- -- ∀ᵖ-intro = λ x→ux x → x→ux x
-- ∀ᵖ-intro = ↓

-- ∀ᵖ-elim :  {ℓ : Level} {A : Set ℓ} {u : A → Set} → ∀ᵖ u → (x : A) → u x
-- ∀ᵖ-elim = ↑

-- -- Existential quantifier
-- data ∃ {ℓ : Level} {A : Set ℓ} : (A → Set) → Set ℓ where
--     ∃-intro : ∀ {u : A → Set} {a : A} → u a → ∃ u

-- ∃ᵖ : {ℓ : Level} {A : Set ℓ} → (A → Set) → Set
-- ∃ᵖ p = ⟪ ∃ p ⟫

-- ∃ᵖ-elim : {ℓ : Level} {A : Set ℓ} {u : A → Set} {q : Set} → (∀ a → u a → q) → ∃ᵖ u → q
-- ∃ᵖ-elim p r with ↑ r
-- ... | ∃-intro x = p _ x

-- ∃ᵖ-intro : {ℓ : Level} {A : Set ℓ} {u : A → Set} {a : A} → u a → ∃ᵖ u
-- ∃ᵖ-intro p = ↓ (∃-intro p)
 