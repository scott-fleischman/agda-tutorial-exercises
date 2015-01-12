module Sets.Parametric where

open import Data.Nat
open import Sets.Enumerated

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Maybe (A : Set) : Set where
  None : Maybe A
  Some : A → Maybe A

data PTree (A : Set) : Set where
  empty : PTree A
  node : PTree A → A → PTree A → PTree A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_


data ⊤ : Set where
  truth : ⊤

data MaybeU (A : Set) : Set where
  mu : ⊤ ⊎ A → MaybeU A


data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  [] : List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ (A B : Set) where
  _∷_ : B → List₁ A B → List₂ A B

l1 : List₁ ⊤ Bool
l1 = []

l2 : List₁ ⊤ Bool
l2 = truth ∷ (true ∷ [])

l3 : List₁ ⊤ Bool
l3 = truth ∷ (false ∷ [])

l4 : List₁ ⊤ Bool
l4 = truth ∷ (true ∷ (truth ∷ (true ∷ [])))

l5 : List₁ ⊤ Bool
l5 = truth ∷ (true ∷ (truth ∷ (false ∷ [])))


data AlterList (A B : Set) : Set where
  [] : AlterList A B
  _∷_ : A → AlterList B A → AlterList A B

al1 : AlterList ⊤ Bool
al1 = []

al2 : AlterList ⊤ Bool
al2 = truth ∷ []

al3 : AlterList ⊤ Bool
al3 = truth ∷ (true ∷ [])

al4 : AlterList ⊤ Bool
al4 = truth ∷ (false ∷ [])


data T4 (A : Set) : Set where
  quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
  zero : A → Square A
  suc : Square (T4 A) → Square A

t0 : Square ℕ
t0 = zero 3

t0' : Square ℕ
t0' = suc (zero (quad 1 2 3 4))

t1 : Square (T4 ℕ)
t1 = zero (quad 1 2 3 4)
