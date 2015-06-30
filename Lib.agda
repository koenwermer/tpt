module Lib where

-------------------------------------------------------------------------------
-----------------  Prelude - partially copied from exercise 2a  ---------------
-------------------------------------------------------------------------------

-- Equality.
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  
cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f refl = refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans refl refl = refl

symm : {a : Set} {x y : a} -> x == y -> y == x
symm refl = refl

proof-irrelevance : ∀{t} {x y : t} {p q : x == y} -> p == q
proof-irrelevance {p = refl} {q = refl} = refl

-- Contradiction type.
data Empty : Set where

-- Reducto ab absurdum.
contradiction : {A : Set} → Empty → A
contradiction ()

-- Negation
Not : Set → Set
Not A = A → Empty

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

data Tuple (a b : Set) : Set where
  _,_ : a -> b -> Tuple a b

fst : {a b : Set} -> Tuple a b -> a
fst (x , y) = x

snd : {a b : Set} -> Tuple a b -> b
snd (x , y) = y

data Bool : Set where
  True : Bool
  False : Bool

--Equality on nats:
_`eq`_ : (n : Nat) -> (m : Nat) -> Either (n == m) (Not (n == m))
Zero `eq` Zero = Left refl
Zero `eq` Succ _ = Right (λ ())
Succ _ `eq` Zero = Right (λ ())
Succ n `eq` Succ m with n `eq` m
Succ n `eq` Succ m | Left r = Left (cong Succ r)
Succ n `eq` Succ m | Right f = Right (λ r -> f (cong unSucc r))
  where
  unSucc : Nat -> Nat
  unSucc Zero = Zero
  unSucc (Succ n) = n
