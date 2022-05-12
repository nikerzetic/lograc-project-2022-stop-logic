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
open import Relation.Binary.PropositionalEquality
open import Function.Base 

------------------------------------------------------------------------
-- Topology on a set X
record topology {ℓ} (X : Set ℓ) : Setω₁ where
    field
        τ : ℙ (ℙ X) -- the subsetset of open subsets of X
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

-- trivial topology
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

-- Proof that B is a base
isBase : {ℓ k : Level} {X : Set ℓ} {I : Set k}
    → (I → ℙ X)
    → Prop
isBase {X = X} {I = I} B = 
    (∀ᵖ λ (x : X) → (∃ᵖ (λ (i : I) → x ∈ B i)))
    ∧ᵖ(∀ᵖ (λ (i : I) → (∀ᵖ λ (j : I) → B i ∩ B j ⊆ᵖ union B)))
    
-- Proof that B is a base for topology T
isBaseOfTopology : {ℓ k : Level} {X : Set ℓ} {I : Set k}
    → (I → ℙ X)
    → topology X 
    → Prop
isBaseOfTopology {X = X} {I = I} B T = 
    ∀ᵖ λ (U : ℙ X) → U ∈ topology.τ T 
        → (U ⊆ᵖ (λ x → x ∈ U → ∃ᵖ λ (i : I) → x ∈ B i ∧ᵖ  B i ⊆ᵖ U))

-- Lemma: inclusion transitivity
∈⊆∈ : {ℓ k : Level} {A : Set ℓ} 
    → (a : A) 
    → (S T : ℙ A)
    → a ∈ S
    → S ⊆ T -- TODO tu imamo tezavo, ker bi zeleli s p 
    → a ∈ T
∈⊆∈ a S T a∈S S⊆T = S⊆T a a∈S 

-- Topology generated by a base
baseGeneratedTopology : {ℓ k : Level} {X : Set ℓ} {I : Set k}
    → (B : I → ℙ X)
    → (isBase B)
    → topology X
baseGeneratedTopology {X = X} {I = I} B ib = 
    record
        {
        τ =  λ (U : ℙ X) → U ≡ᵖ (λ (x : X) → ∃ᵖ (λ (i : I) → x ∈ B i ∧ᵖ B i ⊆ᵖ U))
            -- → ∀ᵖ (λ x → x ∈ U 
            --     → ∃ᵖ (λ (i : I) → x ∈ B i ∧ᵖ B i ⊆ᵖ U))
        ; ∅-open = ∧ᵖ-intro 
            (∀ᵖ-intro (λ x x∈0 → ⊥ᵖ-elim x∈0)) 
            (∀ᵖ-intro (λ x x∈UB 
                → ⊥ᵖ-elim (
                    ∃ᵖ-elim (
                        λ i x∈Bi∧Bi⊆0 → ∀ᵖ-elim (∧ᵖ-elim₂ x∈Bi∧Bi⊆0) x (∧ᵖ-elim₁ x∈Bi∧Bi⊆0)) x∈UB)))
        ; full-open = ∧ᵖ-intro 
            (∀ᵖ-intro (λ x x∈X →  ∃ᵖ-intro {!   !}
            -- (∧ᵖ-intro 
                -- (∃ᵖ-elim (λ i x∈Bi → x∈Bi) (∀ᵖ-elim (∧ᵖ-elim₁ ib) x)) 
                -- {!   !}
            -- )
                -- (∃ᵖ-elim (λ i x∈Bi → ∧ᵖ-intro x∈Bi {!   !} ) (∀ᵖ-elim (∧ᵖ-elim₁ ib) x))
            ))
            (∀ᵖ-intro (λ x x∈UB → ⊤ᵖ-intro))
        ; ∩-open = λ U V Uopen Vopen →  ∧ᵖ-intro
            (∀ᵖ-intro λ x x∈U∩V → {!   !} 
            )
            {!   !}
        ; union-open = λ S i → ∧ᵖ-intro 
            {!   !} 
            {!   !}
        }

-- baseGeneratedTopology : {ℓ : Level} {X : Set ℓ} {I J : Set} 
--     → (B : I → (ℙ X))
--     → ((x : X) → x ∈ union B)
--     → (∀ i j → ∃ᵖ (λ k → (B i ∩ B j) ≡ᵖ B k )) 
--     → topology X
-- baseGeneratedTopology {X = X} {I = I} {J = J} B cov inter = 
--     record 
--         {
--         τ =  λ U → ∃ᵖ (λ (r : J → I) → U ≡ᵖ union (B ∘ r)) 
--         ; ∅-open = {! λ U → ∀ r → (r : J → empty J → I) → empty U ≡ᵖ union (B ∘ r)!}
--         ; full-open = 
--             ∃ᵖ-intro (
--                 ∧ᵖ-intro 
--                 {! λ x → x ∈ (full X) →  !}
--                 --  ⟪ (λ x → x ∈ (full X) →  (cov x)) ⟫
--                 {!   !})
--         ; ∩-open = λ U V U-open V-open → 
--             ∃ᵖ-intro (
--                 ∧ᵖ-intro 
--                 (∀ᵖ-intro λ x p → {!   !}
--                 -- (? ∈ ?) 
--                 -- ∧ᵖ-elim₁ {!   !}
--                 )
--                 (∀ᵖ-intro λ x p → {!   !})
--             )
--         -- U-open U V-open V
--         ; union-open = {!   !}
--         }  