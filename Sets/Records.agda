module Sets.Records where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq

record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ

x : R
x = record { r₁ = true; r₂ = 2 }

r : Bool → ℕ → R
r b n = record { r₁ = b; r₂ = n }

x′ = r true 2

record R′ : Set where
  constructor r′
  field
    r₁ : Bool
    r₂ : ℕ

x″ = r′ true 2
