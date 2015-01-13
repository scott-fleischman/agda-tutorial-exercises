module Functions.Equality_Proofs where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

refl′ : ∀ {A} (a : A) → a ≡ a
refl′ a = refl

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = refl

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc x) = cong suc (+-right-identity x)

+-left-identity : ∀ a → 0 + a ≡ a
+-left-identity a = refl

+-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc x) = tt ∷ (toList x)

from-to : ∀ a → fromList (toList a) ≡ a
from-to zero = refl
from-to (suc a) = cong suc (from-to a)

to-from : ∀ a → toList (fromList a) ≡ a
to-from a = {!!}
