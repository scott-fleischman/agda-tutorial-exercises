module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

-- ⊤ × ⊥ no elemenets
-- ⊥ × ⊥ no elements

⊤⊎⊤ : ⊤ ⊎ ⊤
⊤⊎⊤ = inj₁ tt

⊤⊎⊥ : ⊤ ⊎ ⊥
⊤⊎⊥ = inj₁ tt

-- ⊥ ⊎ ⊥ no elements

ex1 : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
ex1 = inj₂ (inj₁ tt)


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

0≤1 : 1 ≤ 10
0≤1 = s≤s z≤n

3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x


_+_ : ℕ → ℕ → ℕ
_+_ zero n = n
_+_ (suc m) n = m + (suc n)

data _isDoubleOf_ : ℕ → ℕ → Set where
  dub : {n : ℕ} → (n + n) isDoubleOf n

0dub0 : 0 isDoubleOf 0
0dub0 = dub

1notDub0 : 1 isDoubleOf 0 → ⊥
1notDub0 ()

8dub4 : 8 isDoubleOf 4
8dub4 = dub

9notDub4 : 9 isDoubleOf 4 → ⊥
9notDub4 ()


data Odd' : ℕ → Set where
  oddOne : Odd' (suc zero)
  oddSuc : {n : ℕ} → Odd' n → Odd' (suc (suc n))

odd9 : Odd' 9
odd9 = oddSuc (oddSuc (oddSuc (oddSuc oddOne)))

notOdd0 : Odd' 0 → ⊥
notOdd0 ()

notOdd2 : Odd' 2 → ⊥
notOdd2 (oddSuc x) = notOdd0 x

notOdd8 : Odd' 8 → ⊥
notOdd8 (oddSuc (oddSuc (oddSuc x))) = notOdd2 x


data Odd : ℕ → Set
data Even : ℕ → Set

data Even where
  evenZ : Even zero
  evenO : {n : ℕ} → Odd n → Even (suc n)

data Odd where
  oddE : {n : ℕ} → Even n → Odd (suc n)

odd7 : Odd 7
odd7 = oddE (evenO (oddE (evenO (oddE (evenO (oddE evenZ))))))

notEven1 : Even 1 → ⊥
notEven1 (evenO ())

even2 : Even 2
even2 = evenO (oddE evenZ)

notEven3 : Even 3 → ⊥
notEven3 (evenO (oddE (evenO ())))


data _≡_ : ℕ → ℕ → Set where
  eqz : zero ≡ zero
  eqs : ∀ {n m} → n ≡ m → (suc n) ≡ (suc m)

0≡0 : 0 ≡ 0
0≡0 = eqz

0≢1 : 0 ≡ 1 → ⊥
0≢1 ()


data _≠_ : ℕ → ℕ → Set where
  neqz : ∀ {n} → zero ≠ (suc n)
  neqs : ∀ {n m} → n ≠ m → (suc n) ≠ (suc m)

0≠1 : 0 ≠ 1
0≠1 = neqz

1≠1n : 1 ≠ 1 → ⊥
1≠1n (neqs ())



data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} → m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} → m ≤′ n → m ≤′ suc n

infix 4 _≤′_


data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

5+5=10 : 5 + 5 ≡ 10
5+5=10 = sns (sns (sns (sns (sns znn))))

0+5=10 : 0 + 5 ≡ 5
0+5=10 = znn

2+2≠5 : 2 + 2 ≡ 5 → ℕ
2+2≠5 (sns (sns ()))


data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
  minl : ∀ {m} → 0 ⊓ m ≡ 0
  minr : ∀ {n} → n ⊓ 0 ≡ 0
  mins : ∀ {m n k} → m ⊓ n ≡ k → (suc m) ⊓ (suc n) ≡ (suc k)

3⊓5≡3 : 3 ⊓ 5 ≡ 3
3⊓5≡3 = mins (mins (mins (minl)))

3⊓5≢5 : 3 ⊓ 5 ≡ 5 → ⊥
3⊓5≢5 (mins (mins (mins ())))


data _⊔_≡_ : ℕ → ℕ → ℕ → Set where
  maxl : ∀ {m} → m ⊔ 0 ≡ m
  maxr : ∀ {n} → 0 ⊔ n ≡ n
  maxs : ∀ {m n k} → m ⊔ n ≡ k → (suc m) ⊔ (suc n) ≡ (suc k)

3⊔5≡5 : 3 ⊔ 5 ≡ 5
3⊔5≡5 = maxs (maxs (maxs maxr))

3⊔5≢3 : 3 ⊔ 5 ≡ 3 → ⊥
3⊔5≢3 (maxs (maxs (maxs ())))


data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k
  

data _isDoubleOf′_ : ℕ → ℕ → Set where
  dub′ : ∀ {n} → (n + n) isDoubleOf′ n

8dub′4 : 8 isDoubleOf′ 4
8dub′4 = dub′

9dub′4 : 9 isDoubleOf′ 4 → ⊥
9dub′4 ()


data _*_≡_ : ℕ → ℕ → ℕ → Set where
  mulz : ∀ {n} → 0 * n ≡ 0
  muls : ∀ {m n k s} → n + k ≡ s → m * n ≡ k → (suc m) * n ≡ s

0*3≡0 : 0 * 3 ≡ 0
0*3≡0 = mulz

0*3≡1 : 0 * 3 ≡ 1 → ⊥
0*3≡1 = λ ()

0*3≡8 : 0 * 3 ≡ 8 → ⊥
0*3≡8 = λ ()

mp : {n : ℕ} → 3 + n ≡ (suc (suc (suc n)))
mp = sns (sns (sns znn))

1*3≡3 : 1 * 3 ≡ 3
1*3≡3 = muls mp 0*3≡0

2*3≡6 : 2 * 3 ≡ 6
2*3≡6 = muls mp 1*3≡3

3*3≡9 : 3 * 3 ≡ 9
3*3≡9 = muls mp 2*3≡6

-- 1*3≡1 : 1 * 3 ≡ 1 → ⊥
-- 1*3≡1 

data ℕ⁺ : Set where
  one : ℕ⁺
  double : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data _≈_ : ℕ → ℕ⁺ → Set where
  eqone : (suc zero) ≈ one
  eqdub1 : {n : ℕ} → n ≈ one → suc (suc n) ≈ double one
  eqdub+1 : {n : ℕ} {m : ℕ⁺} → n ≈ double m → suc n ≈ double+1 m
  eqdubs : {n : ℕ} {m : ℕ⁺} → n ≈ double+1 m → suc n ≈ double (double m)
  


-- 1 = 1
-- 2 = dub 1
-- 3 = dub+1 1
-- 4 = dub 2
-- 5 = dub+1 2
-- 6 = dub 3
-- 7 = dub+1 3
-- 8 = dub 4
