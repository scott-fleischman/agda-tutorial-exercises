module Revise.Reflection where

open import Data.Nat using (ℕ; _+_; suc; zero; _≤_; s≤s; z≤n; _≟_)
open import Data.Vec using (Vec; []; _∷_; tail; head)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function renaming (_∘_ to _∘f_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

ex : {A : Set} → (A → Set) → Set
ex = Σ _

syntax ex (λ y → x) = y ∣ x

module _ {A : Set} where
  private V = Vec A

  infix 1 _~_
  infixl 3 _∘_

  data _~_ : ∀ {n} → V n → V n → Set where
    zero : [] ~ []
    suc : ∀ {n a} {xs ys : V n} → xs ~ ys → a ∷ xs ~ a ∷ ys
    _∘_ : ∀ {n} {xs ys zs : V n} → xs ~ ys → ys ~ zs → xs ~ zs
    exch : ∀ {n a b} {xs : V n} → a ∷ b ∷ xs ~ b ∷ a ∷ xs

  ~-refl : ∀ {n} {xs : V n} → xs ~ xs
  ~-refl {xs = []} = zero
  ~-refl {xs = _ ∷ []} = suc zero
  ~-refl {xs = _ ∷ _ ∷ xs} = exch ∘ exch
