module Functions.Views.Decidability where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (const; _$_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

1<2 : Dec (1 < 2)
1<2 = yes (s≤s (s≤s z≤n))

1≡1 : Dec (1 ≡ 1)
1≡1 = yes refl

1≡2 : Dec (1 ≡ 2)
1≡2 = no (λ ())

1>2 : Dec (1 > 2)
1>2 = no {!!}

_≟_ : (a b : ℕ) → Dec (a ≡ b)
zero ≟ zero = yes refl
zero ≟ suc b = no (λ ())
suc a ≟ zero = no (λ ())
suc a ≟ suc b with a ≟ b
suc a ≟ suc b | yes x = yes (cong suc x)
suc a ≟ suc b | no x = no {!!}

_≤?_ : (a b : ℕ) → Dec (a ≤ b)
zero ≤? b = yes z≤n
suc a ≤? zero = no (λ ())
suc a ≤? suc b with a ≤? b
suc a ≤? suc b | yes x = yes (s≤s x)
suc a ≤? suc b | no x = no {!!}

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes x ⌋ = true
⌊ no x ⌋ = false
