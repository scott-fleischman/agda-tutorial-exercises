module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)

not : Bool → Bool
not true = false
not false = true


_∧_ : Bool → Bool → Bool
true ∧ x = x
false ∧ _ = false

infixr 6 _∧_


infixr 5 _∨_

_∨_ : Bool → Bool → Bool
false ∨ x = x
true ∨ _ = true


data Answer : Set where
  yes : Answer
  no : Answer
  maybe : Answer


not′ : Answer → Answer
not′ yes = no
not′ no = yes
not′ maybe = maybe


data Quarter : Set where
  east : Quarter
  west : Quarter
  north : Quarter
  south : Quarter

turnLeft : Quarter → Quarter
turnLeft east = north
turnLeft north = west
turnLeft west = south
turnLeft south = east

turnBack : Quarter → Quarter
turnBack x = turnLeft (turnLeft x)

turnRight : Quarter → Quarter
turnRight x = turnLeft (turnBack x)
