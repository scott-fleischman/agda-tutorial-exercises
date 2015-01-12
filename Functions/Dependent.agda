module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc x) = suc (fromℕ x)

_-_ : (n : ℕ) → Fin (suc n) → ℕ
zero - zero = zero
zero - suc ()
suc x - zero = suc x
suc x - suc y = x - y

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = zero
toℕ (suc x) = suc (toℕ x)

fromℕ≤ : ∀ {m n} → m < n → Fin n
fromℕ≤ {zero} {zero} ()
fromℕ≤ {zero} {suc n} _ = zero
fromℕ≤ {suc m} {zero} ()
fromℕ≤ {suc m} {suc n} (s≤s rel) = suc (fromℕ≤ rel)

ex1 : 5 < 6
ex1 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

ex2 : 4 < 5
ex2 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

inject+ : ∀ {m} n → Fin m → Fin (m + n)
inject+ n zero = zero
inject+ n (suc x) = suc (inject+ n x)

four : Fin 66
four = suc (suc (suc (suc zero)))

raise : ∀ {m} n → Fin m → Fin (n + m)
raise zero x = x
raise (suc n) x = suc (raise n x)

head : ∀ {n}{A : Set} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = []
maps (f ∷ fs) (x ∷ xs) = (f x) ∷ (maps fs xs)

replicate : ∀ {n}{A : Set} → A → Vec A n
replicate {zero} x = []
replicate {suc n} x = x ∷ replicate x

map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n
map f xs = maps (replicate f) xs

zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ (zip xs ys)

_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
(x ∷ xs) ! zero = x
(x ∷ xs) ! suc n = xs ! n

