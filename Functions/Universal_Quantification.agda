module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n no = z≤n
≤-trans (s≤s mn) (s≤s no) = s≤s (≤-trans mn no)

total : ∀ m n → m ≤ n ⊎ n ≤ m
total zero _ = inj₁ z≤n
total _ zero = inj₂ z≤n
total (suc m) (suc n) with total m n
… | inj₁ x = inj₁ (s≤s x)
… | inj₂ y = inj₂ (s≤s y)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s z≤n) = z≤n
≤-pred (s≤s (s≤s r)) = s≤s r

≤-mono : ∀ {m n k} → n ≤ m → k + n ≤ k + m
≤-mono {k = zero} r = r
≤-mono {m = m} {n = n} {k = suc k} r = s≤s (≤-mono {m} {n} {k} r)

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n = z≤n
≤-step (s≤s r) = s≤s (≤-step r)

≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
≤′⇒≤ {zero} ≤′-refl = z≤n
≤′⇒≤ {suc a} ≤′-refl = s≤s (≤′⇒≤ {a} ≤′-refl)
≤′⇒≤ (≤′-step r) = ≤-step (≤′⇒≤ r)

z≤′n : ∀ n → zero ≤′ n
z≤′n zero = ≤′-refl
z≤′n (suc n) = ≤′-step (z≤′n _)

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl = ≤′-refl
s≤′s (≤′-step r) = ≤′-step (s≤′s r)

≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
≤⇒≤′ {b = b} z≤n = z≤′n b
≤⇒≤′ (s≤s r) = s≤′s (≤⇒≤′ r)

fin≤ : ∀ {n}(m : Fin n) → toℕ m < n
fin≤ zero = s≤s z≤n
fin≤ (suc m) = s≤s (fin≤ m)
