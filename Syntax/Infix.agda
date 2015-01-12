module Syntax.Infix where

open import Sets.Enumerated using (Bool; true; false)

data BinTree' : Set where
  x : BinTree'
  _+_ : BinTree' → BinTree' → BinTree'

infixr 3 _+_
