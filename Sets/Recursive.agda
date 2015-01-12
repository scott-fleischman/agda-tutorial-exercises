module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data ℕ⁺ : Set where
  one : ℕ⁺
  double : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺
  
data ℕ₂ : Set where
  zero : ℕ₂
  id : ℕ⁺ → ℕ₂

data ℤ⁺ : Set where
  +one : ℤ⁺
  suc : ℤ⁺ → ℤ⁺

data ℤ⁻ : Set where
  -one : ℤ⁻
  pred : ℤ⁻ → ℤ⁻

data ℤ : Set where
  zero : ℤ
  +id : ℤ⁺ → ℤ
  -id : ℤ⁻ → ℤ

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

data BinTreeLeafNat : Set where
  leaf : ℕ → BinTreeLeafNat
  node : BinTreeLeafNat → BinTreeLeafNat → BinTreeLeafNat

data BinTreeNodeNat : Set where
  leaf : BinTreeNodeNat
  node : BinTreeNodeNat → ℕ → BinTreeNodeNat → BinTreeNodeNat

data BinTreeNatBool : Set where
  leaf : ℕ → BinTreeNatBool
  node : BinTreeNatBool → Bool → BinTreeNatBool → BinTreeNatBool

data ListNat : Set where
  empty : ListNat
  cons : ℕ → ListNat → ListNat

data ListSomeNat : Set where
  last : ℕ → ListSomeNat
  const : ℕ → ListSomeNat → ListSomeNat
  
