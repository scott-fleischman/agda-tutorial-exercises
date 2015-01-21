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
to-from [] = refl
to-from (x ∷ xs) = cong (_∷_ tt) (to-from xs)

fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
fromPreserves++ [] b = refl
fromPreserves++ (x ∷ a) b = cong suc (fromPreserves++ a b)

toPreserves++ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
toPreserves++ zero b = refl
toPreserves++ (suc a) b = cong (_∷_ tt) (toPreserves++ a b)

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

+-comm′ : (n m : ℕ) → n + m ≡ m + n
+-comm′ zero n = sym (+-right-identity n)
+-comm′ (suc m) n =
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm′ m n) ⟩
    suc (n + m)
  ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
    (n + suc m)
  ∎

distribʳ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribʳ-*-+ zero b c = refl
distribʳ-*-+ (suc a) b c =
    c + (a + b) * c
  ≡⟨ cong (λ x → c + x) (distribʳ-*-+ a b c) ⟩
    (c + (a * c + b * c))
  ≡⟨ (+-assoc c (a * c) (b * c)) ⟩
    (c + a * c + b * c)
  ∎ 

*-assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-assoc zero b c = refl
*-assoc (suc a) b c =
    (b * c + a * (b * c))
  ≡⟨ {!!} ⟩
    ((b + a * b) * c)
  ∎

*-left-identity : ∀ a → 1 * a ≡ a
*-left-identity zero = refl
*-left-identity (suc a) = cong suc (*-left-identity a)

*-right-identity : ∀ a → a * 1 ≡ a
*-right-identity zero = refl
*-right-identity (suc a) = cong suc (*-right-identity a)

n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 zero = refl
n*0≡0 (suc n) = n*0≡0 n

*-suc : ∀ n m → n + n * m ≡ n * suc m
*-suc zero m = refl
*-suc (suc n) m with *-suc n m
… | r₁ with cong (λ x → m + x) r₁
… | r₂ with +-assoc m n (n * m)
… | r₃ = cong suc {!!}


module trySemiringSolver where

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡-official_)

f : ∀ a b c → a + b * c + 1 ≡-official 1 + c * b + a
f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl
