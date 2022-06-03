------------------------------------------------------------------------
-- Project ???
--
-- Cantor space
------------------------------------------------------------------------

module CantorSpace where

open import Topology.Core
open import Agda.Primitive
open import Topology.PowerSet
open import Data.Product
open import Relation.Binary
open import Data.Nat
open import Data.Bool 
open import Data.List



data foo : Rel (List Bool) lzero  where
    neki : ∀ {l} → foo [] l 
    nekineki : ∀ {x l1 l2} (l1l2 : foo l1 l2) → foo (x ∷ l1) (x ∷ l2)
