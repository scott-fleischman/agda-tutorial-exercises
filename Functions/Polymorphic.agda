module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc xs) = tt ∷ (toList xs)

data Maybe (A : Set) : Set where
  none : Maybe A
  some : A → Maybe A

head : {A : Set} → List A → Maybe A
head [] = none
head (x ∷ xs) = some x

tail : {A : Set} → List A → Maybe (List A)
tail [] = none
tail (x ∷ xs) = some xs

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

maps : {A B : Set} → List (A → B) → List A → List B
maps [] _ = []
maps _ [] = []
maps (f ∷ fs) (x ∷ xs) = f x ∷ maps fs xs

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

id : {A : Set} → A → A
id a = a

aNumber = id {ℕ} (suc zero)

const : {A B : Set} → A → B → A
const a b = a

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

swap : {A B : Set} → A × B → B × A
swap (a , b) = b , a

proj₁ : {A B : Set} → A × B → A
proj₁ (a , b) = a

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

swapS : {A B : Set} → A ⊎ B → B ⊎ A
swapS (inj₁ x) = inj₂ x
swapS (inj₂ x) = inj₁ x

[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[_,_] f g (inj₁ x) = f x
[_,_] f g (inj₂ x) = g x


