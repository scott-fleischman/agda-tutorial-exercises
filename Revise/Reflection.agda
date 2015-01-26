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

  -- permutation relation _~_
  infix 1 _~_
  infixl 3 _∘_

  data _~_ : ∀ {n} → V n → V n → Set where
    zero : [] ~ []
    suc : ∀ {n a} {xs ys : V n} → xs ~ ys → a ∷ xs ~ a ∷ ys
    _∘_ : ∀ {n} {xs ys zs : V n} → xs ~ ys → ys ~ zs → xs ~ zs
    exch : ∀ {n a b} {xs : V n} → a ∷ b ∷ xs ~ b ∷ a ∷ xs

  -- reflexivity and symmetry of _~_
  ~-refl : ∀ {n} {xs : V n} → xs ~ xs
  ~-refl {xs = []} = zero
  ~-refl {xs = _ ∷ []} = suc zero
  ~-refl {xs = _ ∷ _ ∷ xs} = exch ∘ exch

  ~-sym : ∀ {n} {xs ys : V n} → xs ~ ys → ys ~ xs
  ~-sym zero = zero
  ~-sym (suc p) = suc (~-sym p)
  ~-sym (p ∘ p₁) = ~-sym p₁ ∘ ~-sym p
  ~-sym exch = exch

  -- smart constructors
  _∘simp_ : ∀ {n} {xs ys zs : V n} → xs ~ ys → ys ~ zs → xs ~ zs
  zero ∘simp a = a
  suc zero ∘simp a = a
  (exch ∘ exch) ∘simp a = a
  a ∘simp (exch ∘ exch) = a
  a ∘simp b = a ∘ b

  sucSimp : ∀ {n x} {xs ys : V n} → xs ~ ys → x ∷ xs ~ x ∷ ys
  sucSimp zero = suc zero
  sucSimp (suc zero) = exch ∘ exch
  sucSimp (exch ∘ exch) = exch ∘ exch
  sucSimp x = suc x

  -- permutation relation _≈_
  infix 1 _≋_ _≈_
  infixr 3 _↪_
  infixr 4 _∷_

  data Into (n : ℕ) : Set where
    _↪_ : A → V n → Into n

  data _≋_ : ∀ {n} → Into n → V (suc n) → Set where
    zero : ∀ {n x} {xs : V n} → x ↪ xs ≋ x ∷ xs
    suc : ∀ {n x y} {xs : V n} {ys} → x ↪ xs ≋ ys → x ↪ y ∷ xs ≋ y ∷ ys

  data _≈_ : ∀ {n} → V n → V n → Set where
    [] : [] ≈ []
    _∷_ : ∀ {n x} {xs ys : V n} {xxs} → x ↪ xs ≋ xxs → ys ≈ xs → x ∷ ys ≈ xxs

  -- reflexivity of _≈_
  ≈-refl : ∀ {n} {xs : V n} → xs ≈ xs
  ≈-refl {xs = []} = []
  ≈-refl {xs = _ ∷ _} = zero ∷ ≈-refl

  -- _≈_ → _~_
  ~↪ : ∀ {n x} {xs : V n} {ys} → x ↪ xs ≋ ys → x ∷ xs ~ ys
  ~↪ zero = ~-refl
  ~↪ (suc e) = exch ∘simp sucSimp (~↪ e)

  ≈→~ : ∀ {n} {xs ys : V n} → xs ≈ ys → xs ~ ys
  ≈→~ [] = zero
  ≈→~ (x ∷ e) = sucSimp (≈→~ e) ∘simp (~↪ x)

  -- transitivity of _≈_
  ↪-exch : ∀ {n x y} {xs : V n} {xxs yxxs} → x ↪ xs ≋ xxs → y ↪ xxs ≋ yxxs 
    → yxs ∣ (y ↪ xs ≋ yxs) × (x ↪ yxs ≋ yxxs)
  ↪-exch zero zero = _ , zero , suc zero
  ↪-exch zero (suc b) = _ , b , zero
  ↪-exch (suc a) zero = _ , zero , suc (suc a)
  ↪-exch (suc a) (suc b) with ↪-exch a b
  … | _ , s , t = _ , suc s , suc t

  getOut : ∀ {n x} {xs : V n} {xxs xys} → x ↪ xs ≋ xxs → xxs ≈ xys
    → ys ∣ (x ↪ ys ≋ xys) × (xs ≈ ys)
  getOut zero (x₁ ∷ b) = _ , x₁ , b
  getOut (suc a) (x₂ ∷ b) with getOut a b
  … | (l , m , f) with ↪-exch m x₂
  … | s , k , r = s , r , k ∷ f

  infixl 3 _∘≈_

  _∘≈_ : ∀ {n} {xs ys zs : V n} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  [] ∘≈ f = f
  x₁ ∷ e ∘≈ f with getOut x₁ f
  … | a , b , c = b ∷ (e ∘≈ c)
