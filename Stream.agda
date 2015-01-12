{-# OPTIONS --copatterns #-}

module Stream where

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

data ⊤ : Set where
  tt : ⊤

open Stream

ones : Stream ⊤
head ones = ⊤
tail ones = ones

