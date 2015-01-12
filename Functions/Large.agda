module Functions.Large where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

_≤′_ : ℕ → ℕ → Set
zero ≤′ n = ⊤
suc m ≤′ zero = ⊥
suc m ≤′ suc n = m ≤′ n

f : {n m : ℕ} → n ≤ m → n ≤ suc m
f z≤n = z≤n
f (s≤s x) = s≤s (f x)

f′ : {n m : ℕ} → n ≤′ m → n ≤′ suc m
f′ {zero} {m} x = tt
f′ {suc n} {zero} ()
f′ {suc n} {suc m} x = f′ {n} {m} x

_≡_ : ℕ → ℕ → Set
zero ≡ zero = ⊤
zero ≡ suc y = ⊥
suc x ≡ zero = ⊥
suc x ≡ suc y = x ≡ y

_≢_ : ℕ → ℕ → Set
zero ≢ zero = ⊥
zero ≢ suc y = ⊤
suc x ≢ zero = ⊤
suc x ≢ suc y = x ≢ y

mutual
  even : ℕ → Set
  even zero = ⊤
  even (suc x) = odd x

  odd : ℕ → Set
  odd zero = ⊥
  odd (suc x) = even x

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Set
n > m = m < n

_≥_ : ℕ → ℕ → Set
n ≥ m = m ≤ n

¬ : Set → Set
¬ A = A → ⊥

Fin₀ : ℕ → Set
Fin₀ zero = ⊥
Fin₀ (suc x) = ⊤ ⊎ Fin₀ x
