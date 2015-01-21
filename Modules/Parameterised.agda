module Modules.Parameterised where

open import Data.Nat

module X where
  module Y (x₁ : ℕ) where
    y₁ = suc x₁
    y₂ = suc y₁

  x₂ = suc (suc (Y.y₁ 10))
  x₂′ = suc (Y.y₂ 10)

module X′ where
  module Y (x₁ : ℕ) where
    y₁ = suc x₁
    y₂ = suc y₁

  x₂ = suc (Y.y₂ 10)

  module Y′ = Y 10

  x₂′ = suc Y′.y₂
  
module X″ where
  module Y (x₁ : ℕ) where
    y₁ = suc x₁
    y₂ = suc y₁

  x₂ = suc (Y.y₂ 10)

  open module Y′ = Y 10

  x₂′ = suc y₂


