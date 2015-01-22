module Application.Algebra where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)

import Relation.Binary.EqReasoning as EqR

record IsSemigroup {A : Set} (_∙_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

ℕ+-isSemigroup : IsSemigroup _+_
ℕ+-isSemigroup = record { assoc = ap } where
  ap : ∀ x y z → (x + y) + z ≡ x + (y + z)
  ap zero _ _ = refl
  ap (suc x) y z = cong suc (ap x y z)

module Usage₁ where
  open IsSemigroup

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc ℕ+-isSemigroup n 1 1

module Usage₂ where
  open IsSemigroup ℕ+-isSemigroup

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1

module Usage₃ where
  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1 where
    open IsSemigroup ℕ+-isSemigroup

record IsMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identity : (∀ x → ε ∙ x ≡ x) × (∀ x → x ∙ ε ≡ x)

  open IsSemigroup isSemigroup public

ℕ+0-isMonoid : IsMonoid _+_ 0
ℕ+0-isMonoid = record { identity = monoidId; isSemigroup = ℕ+-isSemigroup } where
  monoidId = (λ x → refl) , r0 where
    r0 : (x : ℕ) → x + 0 ≡ x
    r0 zero = refl
    r0 (suc x) = cong suc (r0 x)

module Usage₄ where
  ex : ∀ n → (n + 0) + n ≡ n + n
  ex n = cong (λ x → x + n) (proj₂ identity n) where
    open IsMonoid ℕ+0-isMonoid
    
  ex′ : ∀ n → (n + 0) + n ≡ n + n
  ex′ n = assoc n 0 n where
    open IsMonoid ℕ+0-isMonoid

Op₂ : Set → Set
Op₂ A = A → A → A

record IsSemigroup′ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

Op₁ : Set → Set
Op₁ A = A → A

Associative : {A : Set} → Op₂ A → Set
Associative _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

record IsSemigroup″ {A : Set} (_∙_ : Op₂ A) : Set where
  field
    assoc : Associative _∙_
    
