module Sets.Parameters_vs_Indicies where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl : m ≤′ m
  ≤′-step : {n : ℕ} → m ≤′ n → m ≤′ suc n
  
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

data _∈_ {A : Set} (x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

data _⊆_ {A : Set} : List A → List A → Set where
  z : ∀ {ys} → [] ⊆ ys
  s : ∀ {x xs ys} → x ∈ x ∷ xs → xs ⊆ ys → x ∈ ys → x ∷ xs ⊆ ys

infix 5 _⊆_

sub1 : [] ⊆ 1 ∷ []
sub1 = z

sub2 : 1 ∷ [] ⊆ 1 ∷ []
sub2 = s first z first

sub2a : 1 ∷ [] ⊆ 2 ∷ 1 ∷ []
sub2a = s first z (later first)

sub2b : 1 ∷ [] ⊆ 1 ∷ 2 ∷ []
sub2b = s first z first

sub2c : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ []
sub2c = s first (s first z (later first)) first

sub3 : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
sub3 = s first (s first z (later first)) first

sub3b : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
sub3b = s first (s first z (later first)) first

nin1 : 1 ∈ [] → ⊥
nin1 ()

sub4a : 1 ∷ [] ⊆ [] → ⊥
sub4a (s x x₁ ())

sub4 : 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] → ⊥
sub4 (s x (s x₁ (s x₂ x₃ (later (later ()))) x₅) x₆)

