module Sets.Mutual where

open import Sets.Enumerated using (Bool; true; false)
open import Syntax.Decimal_Naturals using (ℕ; zero; suc)

data L : Set
data M : Set

data L where
  nil : L
  _∷_ : ℕ → M → L

data M where
  _∷_ : Bool → L → M


data FinTree : Set
data FinTreeChildren : Set

data FinTree where
  leaf : FinTree
  node : FinTreeChildren → FinTree

data FinTreeChildren where
  end : FinTreeChildren
  add : FinTree → FinTreeChildren → FinTreeChildren


data IntExp : Set
data IntUnOp : Set
data IntBinOp : Set

data IntExp where
  num : ℕ → IntExp
  unOp : IntUnOp → IntExp
  binOp : IntBinOp → IntExp

data IntUnOp where
  neg : IntExp → IntUnOp

data IntBinOp where
  _plus_ : IntExp → IntExp → IntBinOp
  _times_ : IntExp → IntExp → IntBinOp

