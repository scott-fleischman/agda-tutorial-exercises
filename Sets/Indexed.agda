module Sets.Indexed where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc : (n : ℕ) → Fin n → Fin (suc n)

data Boolie : Bool → Set where
  bt : (true : Bool) → Boolie true

data Evens : ℕ → Set where
  ez : (n : ℕ) → Evens n
  dub : (n : ℕ) → Evens n → Evens (suc (suc n))

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)


data BubBub (A B : Set) : Bool → Set where
  bba : (a : A) → BubBub A B false
  bbb : (b : B) → BubBub A B true
