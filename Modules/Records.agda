module Modules.Records where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ

x : R
x = record { r₁ = true; r₂ = 2 }

module SimpleOpening where
  open R

  y : Bool
  y = r₁ x

module AppliedOpening where
  open R x

  y : Bool
  y = r₁

module AppliedOpening′ where
  y : Bool
  y = r₁ where
    open R x
