module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 6 _+_

-- pred : ℕ → ℕ
-- pred zero = zero
-- pred (suc n) = n

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero ∸ n = zero
m ∸ zero = m
(suc m) ∸ (suc n) = m ∸ n

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + m * n

infixl 6 _⊔_
_⊔_ : ℕ → ℕ → ℕ
zero ⊔ n = n
m ⊔ zero = m
(suc m) ⊔ (suc n) = suc (m ⊔ n)

infixl 7 _⊓_
_⊓_ : ℕ → ℕ → ℕ
zero ⊓ n = zero
m ⊓ zero = zero
(suc m) ⊓ (suc n) = suc (m ⊓ n)

⌊_/2⌋ : ℕ → ℕ
⌊ zero /2⌋ = zero
⌊ suc zero /2⌋ = zero
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

odd : ℕ → Bool
odd zero = false
odd (suc zero) = true
odd (suc (suc n)) = odd n
  
even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

not : Bool → Bool
not false = true
not true = false

mutual
  odd′ : ℕ → Bool
  odd′ zero = false
  odd′ (suc n) = not (even′ n)

  even′ : ℕ → Bool
  even′ zero = true
  even′ (suc n) = not (odd′ n)

_≡?_ : ℕ → ℕ → Bool
zero ≡? zero = true
zero ≡? suc n = false
suc n ≡? zero = false
suc n ≡? suc m = n ≡? m

_≤?_ : ℕ → ℕ → Bool
zero ≤? n = true
suc n ≤? zero = false
suc n ≤? suc m = n ≤? m


open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)

from : ℕ₂ → ℕ
from zero = zero
from (id one) = suc zero
from (id (double n)) = (suc (suc zero)) * (from (id n))
from (id (double+1 n)) = suc ((suc (suc zero)) * (from (id n)))


data ℤ : Set where
  zero : ℤ
  pos+1 : ℕ → ℤ
  neg-1 : ℕ → ℤ

_+z_ : ℤ → ℤ → ℤ
zero +z y = y
pos+1 x +z zero = pos+1 x
pos+1 x +z pos+1 y = pos+1 (x + y)
pos+1 zero +z neg-1 zero = zero
pos+1 zero +z neg-1 (suc y) = neg-1 y
pos+1 (suc x) +z neg-1 zero = pos+1 x
pos+1 (suc x) +z neg-1 (suc y) = pos+1 x +z neg-1 y
neg-1 x +z zero = neg-1 x
neg-1 zero +z pos+1 zero = zero
neg-1 zero +z pos+1 (suc y) = pos+1 y
neg-1 (suc x) +z pos+1 zero = neg-1 x
neg-1 (suc x) +z pos+1 (suc y) = neg-1 x +z pos+1 y
neg-1 x +z neg-1 y = neg-1 (x + y)

_-z_ : ℤ → ℤ → ℤ
zero -z zero = zero
zero -z pos+1 x = neg-1 x
zero -z neg-1 x = pos+1 x
pos+1 x -z zero = pos+1 x
pos+1 zero -z pos+1 zero = zero
pos+1 zero -z pos+1 (suc y) = neg-1 y
pos+1 (suc x) -z pos+1 zero = pos+1 x
pos+1 (suc x) -z pos+1 (suc y) = pos+1 x -z pos+1 y
pos+1 x -z neg-1 y = pos+1 (x + y)
neg-1 x -z zero = neg-1 x
neg-1 x -z pos+1 y = neg-1 (x + y)
neg-1 zero -z neg-1 zero = zero
neg-1 (suc x) -z neg-1 zero = neg-1 x
neg-1 zero -z neg-1 (suc y) = pos+1 y
neg-1 (suc x) -z neg-1 (suc y) = neg-1 x -z neg-1 y

-- not correct
_*z_ : ℤ → ℤ → ℤ
zero *z y = zero
pos+1 x *z zero = zero
pos+1 zero *z pos+1 y = pos+1 y
pos+1 (suc x) *z pos+1 y = pos+1 y +z (pos+1 x *z pos+1 y)
pos+1 zero *z neg-1 y = neg-1 y
pos+1 (suc x) *z neg-1 y = neg-1 (suc x * y)
neg-1 x *z zero = zero
neg-1 zero *z pos+1 y = neg-1 y
neg-1 (suc x) *z pos+1 y = neg-1 (suc x * y)
neg-1 x *z neg-1 y = pos+1 (x * y)


data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

mirror : BinTree → BinTree
mirror leaf = leaf
mirror (node ℓ r) = node (mirror r) (mirror ℓ)
