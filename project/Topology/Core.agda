------------------------------------------------------------------------
-- Project ???
--
-- Sierpinski space
------------------------------------------------------------------------

{-# OPTIONS --prop #-}

module Topology.Core where

open import Agda.Primitive
open import Topology.Logic
open import Topology.PowerSet

-- Topology on a set X
record topology {ℓ} (X : Set ℓ) : Setω₁ where
    field
        τ : ℙ (ℙ X) -- the subsetset of open subsets of X
        -- zamenjal 𝒪 z τ, ker VS Code prvega razume kot dva znaka in zato linter ne dela
        ∅-open : empty X ∈ τ
        full-open : full X ∈ τ
        ∩-open : ∀ U V → U ∈ τ → V ∈ τ → U ∩ V ∈ τ
        union-open : ∀ {ℓ : Level} {I : Set ℓ} (S : I → ℙ X) → (∀ i → S i ∈ τ) → union S ∈ τ

discrete-topology : {ℓ : Level} (X : Set ℓ) → topology X
discrete-topology X =
    record
        { τ = λ _ → ⊤ᵖ
        ; ∅-open = ⊤ᵖ-intro
        ; full-open = ⊤ᵖ-intro
        ; ∩-open = λ _ _ _ _ → ⊤ᵖ-intro
        ; union-open = λ _ _ → ⊤ᵖ-intro
        }

indiscrete-topology : {ℓ : Level} (X : Set ℓ) → topology X
indiscrete-topology X =
    record
        { τ = λ U → ∃ᵖ U → ∀ᵖ U
        ; ∅-open = λ p → ⊥ᵖ-elim (∃ᵖ-elim (λ { a ()}) p)
        ; full-open = λ p → ∀ᵖ-intro (λ _ → ⊤ᵖ-intro)
        ; ∩-open =
            λ U V p q r →
            ∀ᵖ-intro (λ x →
                ∧ᵖ-intro
                (∀ᵖ-elim (p (∃ᵖ-elim (λ { a (∧ᵖ-intro a∈U _) → ∃ᵖ-intro a∈U}) r)) x)
                (∀ᵖ-elim (q (∃ᵖ-elim (λ { a (∧ᵖ-intro _ a∈V) → ∃ᵖ-intro a∈V}) r)) x))
        ; union-open =
            λ S Si-open p →
            ∀ᵖ-intro (λ x →
                ∃ᵖ-elim (λ y a∈∪S →
                ∃ᵖ-elim (λ i y∈Si →
                    ∃ᵖ-intro (∀ᵖ-elim (Si-open i (∃ᵖ-intro y∈Si)) x)) a∈∪S) p)
        }

