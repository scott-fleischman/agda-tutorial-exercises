module VVV where

data Nat : Set where
 ze : Nat
 su : Nat -> Nat

_+_ : Nat -> Nat -> Nat
ze + y = y
su x + y = su (x + y)

data Vec (X : Set) : Nat -> Set where
 [] : Vec X ze
 _,_ : {n : Nat} -> X -> Vec X n -> Vec X (su n)

data _==_ {A : Set}(a : A) : {B : Set} -> B -> Set where  refl : a == a

_++_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m + n)
[] ++ ys = ys
(x , xs) ++ ys = x , (xs ++ ys)

record _*_ (S T : Set) : Set where
 constructor _,_
 field
   fst : S
   snd : T
open _*_ public

resp1 : {A : Set}{B : A -> Set}
 (f : (a : A) -> B a)
 {a a' : A} -> a == a' ->
 f a == f a'
resp1 f refl = refl

resp3 : {A : Set}{B : A -> Set}{C : (a : A)(b : B a) -> Set}{D : (a : A)(b : B a)(c : C a b) -> Set}  (f : (a : A)(b : B a)(c : C a b) -> D a b c) ->  {a a' : A} -> a == a' ->  {b : B a}{b' : B a'} -> b == b' ->  {c : C a b}{c' : C a' b'} -> c == c' ->  f a b c == f a' b' c'
resp3 f refl refl refl = refl

vc : {X : Set}(n : Nat)(x : X) -> Vec X n -> Vec X (su n)
vc n x xs = x , xs

vass : {X : Set}{l m n : Nat}(xs : Vec X l)(ys : Vec X m)(zs : Vec X n) ->  (((l + m) + n) == (l + (m + n))) *  (((xs ++ ys) ++ zs) == (xs ++ (ys ++ zs)))
vass [] ys zs = refl , refl
vass (x , xs) ys zs with vass xs ys zs
... | q , q' = (resp1 su q) , resp3 vc q refl q'
