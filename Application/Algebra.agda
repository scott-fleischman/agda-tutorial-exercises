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

Commutative : {A : Set} → Op₂ A → Set _
Commutative _∙_ = ∀ x y → x ∙ y ≡ y ∙ x

LeftIdentity : {A : Set} → A → Op₂ A → Set _
LeftIdentity ε _∙_ = ∀ x → ε ∙ x ≡ x

RightIdentity : {A : Set} → A → Op₂ A → Set _
RightIdentity ε _∙_ = ∀ x → x ∙ ε ≡ x

Identity : {A : Set} → A → Op₂ A → Set _
Identity ε _∙_ = (LeftIdentity ε _∙_) × (RightIdentity ε _∙_)

record IsCommutativeMonoid′ {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isMonoid : IsMonoid _∙_ ε
    comm : Commutative _∙_

record IsCommutativeMonoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup _∙_
    identityˡ : LeftIdentity ε _∙_
    comm : Commutative _∙_

  open IsSemigroup isSemigroup public

  identity : Identity ε _∙_
  identity = (identityˡ , identityʳ)
    where
    open EqR (setoid A)
    
    identityʳ : RightIdentity ε _∙_
    identityʳ = λ x → begin
      (x ∙ ε) ≈⟨ comm x ε ⟩
      (ε ∙ x) ≈⟨ identityˡ x ⟩
      x       ∎

    isMonoid : IsMonoid _∙_ ε
    isMonoid = record
      { isSemigroup = isSemigroup
      ; identity = identity
      }

LeftInverse : {A : Set} → (ε : A) → (x⁻¹ : A) → Op₂ A → Set _
LeftInverse ε x⁻¹ _∙_ = ∀ x → x⁻¹ ∙ x ≡ ε

RightInverse : {A : Set} → (ε : A) → (x⁻¹ : A) → Op₂ A → Set _
RightInverse ε x⁻¹ _∙_ = ∀ x → x ∙ x⁻¹ ≡ ε

Inverse : {A : Set} → (ε : A) → (x⁻¹ : A) → Op₂ A → Set _
Inverse ε x⁻¹ _∙_ = (LeftInverse ε x⁻¹ _∙_) × (RightInverse ε x⁻¹ _∙_)

record IsGroup {A : Set} (_∙_ : A → A → A) (ε : A) (x⁻¹ : A) : Set where
  field
    isMonoid : IsMonoid _∙_ ε
    inverse : Inverse ε x⁻¹ _∙_

record IsAbelianGroup {A : Set} (_∙_ : A → A → A) (ε : A) (x⁻¹ : A) : Set where
  field
    isCommutativeMonoid : IsCommutativeMonoid _∙_ ε
    inverse : Inverse ε x⁻¹ _∙_

record Semigroup : Set₁ where
  infixl 7 _∙_
  field
    Carrier : Set
    _∙_ : Op₂ Carrier
    isSemigroup : IsSemigroup _∙_

  open IsSemigroup isSemigroup public

ℕ-semigroup : Semigroup
ℕ-semigroup = record
  { Carrier = ℕ
  ; _∙_ = _+_
  ; isSemigroup = ℕ+-isSemigroup
  }

record Monoid : Set₁ where
  infixl 7 _∙_
  field
    Carrier : Set
    _∙_ : Op₂ Carrier
    ε : Carrier
    isMonoid : IsMonoid _∙_ ε

module MonoidOperations (m : Monoid) where
  open Monoid m
  
  infixr 7 _×′_

  _×′_ : ℕ → Carrier → Carrier
  0 ×′ x = ε
  suc n ×′ x = x ∙ n ×′ x

import Algebra.FunctionProperties using (Op₁; Op₂)
import Algebra.FunctionProperties using (Associative; Commutative; LeftIdentity; RightIdentity; Identity)
import Algebra.Structures using (IsSemigroup; IsMonoid; IsCommutativeMonoid)
import Algebra using (Semigroup; Monoid; CommutativeMonoid)
import Algebra.Operations

import Data.Nat.Properties using (isCommutativeSemiring)

module StdLibUsage where
  open import Algebra.Structures as A using (IsCommutativeMonoid)
  open import Data.Nat.Properties using (isCommutativeSemiring)

  open A.IsCommutativeSemiring
  open A.IsCommutativeMonoid (+-isCommutativeMonoid isCommutativeSemiring)

  ex : ∀ n → (n + 1) + 1 ≡ n + 2
  ex n = assoc n 1 1

