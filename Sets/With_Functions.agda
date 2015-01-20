module Sets.With_Functions where

open import Data.Nat
open import Data.Empty using (⊥)
open import Data.List using (List; length)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

data Even : ℕ → Set where
  double : ∀ n → Even (n + n)

data Even′ (m : ℕ) : Set where
  double : ∀ n → m ≡ n + n → Even′ m

toEven : ∀ {m} → Even′ m → Even m
toEven {.(n + n)} (double n refl) = double n

toEven′ : ∀ {m} → Even m → Even′ m
toEven′ {.(n + n)} (double n) = double n refl

-- lemmas
suc-+ : ∀ n m → suc (n + m) ≡ n + suc m
suc-+ zero m = refl
suc-+ (suc n) m = cong suc (suc-+ n m)

prev-≡ : ∀ {n m} → suc n ≡ suc m → n ≡ m
prev-≡ {.m} {m} refl = refl

nextEven′ : ∀ {n} → Even′ n → Even′ (suc (suc n))
nextEven′ {.(n₁ + n₁)} (double n₁ refl) = double (suc n₁) (cong suc (suc-+ n₁ n₁))

prevEven′ : ∀ {n} → Even′ (suc (suc n)) → Even′ n
prevEven′ (double zero ())
prevEven′ (double (suc n) x) = double n (prev-≡ (trans (prev-≡ x) (sym (suc-+ n n))))

¬Even′1 : Even′ 1 → ⊥
¬Even′1 (double zero ())
¬Even′1 (double (suc zero) ())
¬Even′1 (double (suc (suc n)) ())

isEven′ : (n : ℕ) → Dec (Even′ n)
isEven′ zero = yes (double zero refl)
isEven′ (suc zero) = no ¬Even′1
isEven′ (suc (suc n)) with isEven′ n
isEven′ (suc (suc n)) | yes p = yes (nextEven′ p)
isEven′ (suc (suc n)) | no ¬p = no (λ x → ¬p (prevEven′ x))

¬Even1 : ∀ {n} → Even n → n ≡ 1 → ⊥
¬Even1 (double zero) ()
¬Even1 (double (suc zero)) ()
¬Even1 (double (suc (suc n))) ()

nextEven : ∀ {n} → Even n → Even (suc (suc n))
nextEven {.(n + n)} (double n) rewrite cong suc (suc-+ n n) = double (suc n)

prevEven : ∀ {n} → Even (suc (suc n)) → Even n
prevEven e = toEven (prevEven′ (toEven′ e))

isEven : (n : ℕ) → Dec (Even n)
isEven zero = yes (double zero)
isEven (suc zero) = no (λ x → ¬Even1 x refl)
isEven (suc (suc n)) with isEven n
isEven (suc (suc n)) | yes p = yes (nextEven p)
isEven (suc (suc n)) | no ¬p = no (λ x → ¬p (prevEven x))

data _≤″_ : ℕ → ℕ → Set where
  diff : ∀ i j → i ≤″ j + i

infix 4 _≤″_

data Vec (A : Set) : ℕ → Set where
  vec : (x : List A) → Vec A (length x)


