module Modules.Data where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

x₁ : ℕ
x₁ = ℕ.suc ℕ.zero

x₂ : ℕ
x₂ = suc zero

data ℕ′ : Set where
  zero : ℕ′
  suc : ℕ′ → ℕ′

const : {A B : Set} → A → B → A
const a b = a

y₁ : ℕ′
y₁ = const ℕ′.zero (ℕ.suc ℕ.zero)

y₂ : ℕ′
y₂ = const zero (ℕ.suc zero)

-- y₃ : ℕ′
-- y₃ = const zero (suc zero)

-- y₄ : ℕ′
-- y₄ = const zero (suc ℕ.zero)
