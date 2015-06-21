
module Project where

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

-------------------------------------------------------------------------------
----------------------               Syntax              ----------------------
-------------------------------------------------------------------------------

-- Natural numbers suffice as identifiers for variables
Variable = Nat

data Type : Set where
  NAT     : Type
  BOOL    : Type
  <>      : Type
  POINTER : Type -> Type

-- Terms of the language
data Term : Type -> Set where
  -- Basic stuff
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- We just use natural numbers as variables
  var           : {ty : Type} -> Nat -> Term (POINTER ty)

  -- Create a new cell with an initial value REPLACED BY VAR
  --ref           : {ty : Type} -> Term ty -> Term (POINTER ty)

  -- Redirecting a pointer to another cell, similar to "=" in the book
  _=>_          : {ty : Type} -> Term (POINTER ty) -> Term (POINTER ty) -> Term <>
  -- Storing a value in a cell
  _:=_          : {ty : Type} -> Term (POINTER ty) -> Term ty -> Term <>
  -- Sequencing side effects
  _%_           : Term <> -> Term <> -> Term <> -- ; not allowed as operator :'(
  -- Dereferencing
  !_            : {ty : Type} -> Term (POINTER ty) -> Term ty
  -- Nothing
  <>            : Term <>

-- We need an environment to keep track of the types of stored variables
Pointer = Nat
TypeEnv = Pointer -> Type

-- The environment returns the actual expressions, and is given a type environment that matches the expressions
-- The state consists of a matching environment and type environment
data State : TypeEnv -> Set where
  state : (f : TypeEnv) -> ((p : Pointer) -> (Term (f p))) -> State f

-- Some usefull functions on state:

-- Retrieves the values of a given pointer from the state, and rewrites the type using equational reasoning
getEq : {typeOf : TypeEnv} {ty : Type} -> State typeOf -> (n : Pointer) -> typeOf n == ty -> Term ty
getEq {typeOf} (state .typeOf env) n refl = env n

-- Redirects a pointer to another cell
redirect : {typeOf : TypeEnv} -> (n : Pointer) -> (m : Pointer) -> typeOf n == typeOf m -> State typeOf -> State typeOf
redirect n m r (state typeOf env) = state typeOf env'
  where
  env' : (p : Pointer) -> (Term (typeOf p))
  env' p with p `eq` n
  env' p | Left t with trans (cong typeOf t) r
  env' .n | Left refl | y = getEq (state typeOf env) m (symm y)
  env' p | Right _ = env p

-- Stores an expression in a cell
store : {ty : Type} {typeOf : TypeEnv} -> (n : Pointer) -> (t : Term ty) -> typeOf n == ty -> State typeOf -> State typeOf
store n t refl (state typeOf env) = state typeOf env'
  where
  env' : (p : Pointer) -> (Term (typeOf p))
  env' p with p `eq` n
  env' .n | Left refl = t
  env' p | Right _ = env p

-- Gets an expression from a cell
get : {typeOf : TypeEnv} -> State typeOf -> (n : Pointer) -> Term (typeOf n)
get s n = getEq s n refl

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  vnat : Nat -> Value NAT
  vvar : {ty : Type} -> Nat -> Value (POINTER ty)
  vnothing : Value <>

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat k ⌝ = natTerm k
⌜ vvar n ⌝ = var n
⌜ vnothing ⌝ = <>


-------------------------------------------------------------------------------
----------------------             Small-step            ----------------------
-------------------------------------------------------------------------------

data Step  : {ty : Type} {f : TypeEnv} -> State f -> Term ty → State f -> Term ty → Set where
  -- Pure thingies leave the state unchanged, but may contain non-pure expressions and propagate the changes made by those
  E-If-True : forall {f : TypeEnv} {s : State f} {ty} {t1 t2 : Term ty} -> Step s (if true then t1 else t2) s t1
  E-If-False : forall {f : TypeEnv} {s : State f} {ty} {t1 t2 : Term ty} -> Step s (if false then t1 else t2) s t2
  E-If-If : forall {f : TypeEnv} {s s' : State f} {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step s t1 s' t1' -> 
    Step s (if t1 then t2 else t3) s' (if t1' then t2 else t3)
  E-Succ       : forall {f : TypeEnv} {s s' : State f} {t t' : Term NAT} -> Step {NAT} s t s' t' -> Step {NAT} s (succ t) s' (succ t')
  E-IsZeroZero : forall {f : TypeEnv} {s : State f} -> Step s (iszero zero) s true
  E-IsZeroSucc : forall {f : TypeEnv} {s : State f} {v : Value NAT} -> Step s (iszero (succ ⌜ v ⌝)) s false
  E-IsZero     : forall {f : TypeEnv} {s s' : State f} {t t' : Term NAT} -> Step s t s' t' -> Step s (iszero t) s' (iszero t')
  -- Pointer thingies may use or change the state
  -- We can redirect pointers to other cells iff the the types match. Both arguments of => must be completely evaluated
  E-=> : forall {typeOf : TypeEnv} {s : State typeOf} {ty : Type} {n m : Nat} -> (r : typeOf n == ty) (r' : typeOf m == ty) -> Step s (_=>_ {ty} (var n) (var m)) (redirect n m (trans r (symm r')) s) <>
  -- We first evaluate the first argument of => to a pointer
  E-=>-Fst : forall {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t1 t1' t2 : Term (POINTER ty)} -> Step s t1 s' t1' -> Step s (t1 => t2) s' (t1' => t2)
  -- If the first argument is a pointer, we evaluate the second argument
  E-=>-Snd : forall {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {n : Nat} {t2 t2' : Term (POINTER ty)} -> Step s t2 s' t2' -> Step s (var n => t2) s' (var n => t2')
  -- We can store any expression in a cell, as long as the types match
  E-:= : forall {typeOf : TypeEnv} {s : State typeOf} {ty : Type} {n : Nat} {t : Term ty} -> (r : typeOf n == ty) -> Step s (_:=_ {ty} (var n) t) (store n t r s) <>
  -- We must first evaluate the first argument of := to a pointer
  E-:=-Fst : forall {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t1 t1' : Term (POINTER ty)} {t2 : Term ty} -> Step s t1 s' t1' -> Step s (t1 := t2) s' (t1' := t2)
  -- We can eliminate sequencing only if the first argument if completely evaluated
  E-% : forall {typeOf : TypeEnv} {s : State typeOf} {t : Term <>} -> Step s (<> % t) s t
  -- Of course, sequencing evaluates the first argument first
  È-%-Fst : forall {typeOf : TypeEnv} {s s' : State typeOf} {t1 t1' t2 : Term <>} -> Step s t1 s' t1' -> Step s (t1 % t2) s' (t1' % t2)
  -- Dereferencing just gets the stored expression from the state
  E-! : forall {typeOf : TypeEnv} {s : State typeOf} {n : Nat} -> Step s (! (var n)) s (get s n)
  -- We must first evaluate the pointer expression to normal form before we can dereference it
  E-!-Fst : forall {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t t' : Term (POINTER ty)} -> Step s t s' t' -> Step s (! t) s' (! t')

valuesDoNotStep : forall {ty : Type} {f : TypeEnv} {s1 s2 : State f} -> (v : Value ty) (t : Term ty) -> Step s1 ⌜ v ⌝  s2 t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : forall {typeOf : TypeEnv} {s s' : State typeOf} -> (n : Nat) -> (t : Term NAT) -> Step s (natTerm n) s' t -> Empty
  lemma Zero t ()
  lemma {f} {s} {s'} (Succ n) .(succ t') (E-Succ {.f} {.s} {.s'} {.( ⌜ vnat n ⌝)} {t'} step) = lemma n t' step
valuesDoNotStep (vvar n) t ()
valuesDoNotStep vnothing t ()

-- Proving the small step semantics are deterministic
deterministic : forall {ty} {f : TypeEnv} {s s' s'' : State f} {t t' t'' : Term ty} -> Step s t s' t' -> Step s t s'' t'' → t' == t''
deterministic E-If-True E-If-True = refl
deterministic E-If-True (E-If-If ())
deterministic E-If-False E-If-False = refl
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-If-If step1) (E-If-If step2) = cong (λ x -> if x then _ else _) (deterministic step1 step2)
deterministic (E-Succ steps1) (E-Succ steps2) = cong succ (deterministic steps1 steps2)
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic (E-IsZeroSucc {_} {_} {v}) step2 = lemma v _ step2
  where
  lemma : (v : Value NAT) (t : Term BOOL) -> Step _ (iszero (succ ⌜ v ⌝)) _ t -> false == t
  lemma (vnat x) true ()
  lemma (vnat x) false step = refl
  lemma (vnat x) (if t then t₁ else t₂) ()
  lemma (vnat x) (iszero ._) (E-IsZero (E-Succ step)) = contradiction (valuesDoNotStep (vnat x) _ step)
  lemma (vnat x) (! p) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic step1 (E-IsZeroSucc {_} {_} {v}) = lemma v _ step1
  where
  lemma : (v : Value NAT) (t : Term BOOL) -> Step _ (iszero (succ ⌜ v ⌝)) _ t -> t == false
  lemma (vnat x) true ()
  lemma (vnat x) false step = refl
  lemma (vnat x) (if t then t₁ else t₂) ()
  lemma (vnat x) (iszero ._) (E-IsZero (E-Succ step)) = contradiction (valuesDoNotStep (vnat x) _ step)
  lemma (vnat x) (! p) ()
deterministic (E-IsZero step1) (E-IsZero step2) = cong iszero (deterministic step1 step2)
deterministic (E-=> r r') (E-=> r0 r1) = refl
deterministic (E-=> r r') (E-=>-Fst ())
deterministic (E-=> r r') (E-=>-Snd ())
deterministic (E-=>-Fst ()) (E-=> r r')
deterministic (E-=>-Fst step1) (E-=>-Fst step2) = cong _ (deterministic step1 step2)
deterministic (E-=>-Fst ()) (E-=>-Snd step2)
deterministic (E-=>-Snd ()) (E-=> r r')
deterministic (E-=>-Snd step1) (E-=>-Fst ())
deterministic (E-=>-Snd step1) (E-=>-Snd step2) = cong _ (deterministic step1 step2)
deterministic (E-:= r) (E-:= r') = refl
deterministic (E-:= r) (E-:=-Fst ())
deterministic (E-:=-Fst ()) (E-:= r)
deterministic (E-:=-Fst step1) (E-:=-Fst step2) = cong _ (deterministic step1 step2)
deterministic E-% E-% = refl
deterministic E-% (È-%-Fst ())
deterministic (È-%-Fst ()) E-%
deterministic (È-%-Fst step1) (È-%-Fst step2) = cong _ (deterministic step1 step2)
deterministic E-! E-! = refl
deterministic E-! (E-!-Fst ())
deterministic (E-!-Fst ()) E-!
deterministic (E-!-Fst step1) (E-!-Fst step2) = cong _ (deterministic step1 step2)

-- Types are preserved during evaluation
preservation : forall {ty : Type} {f : TypeEnv} {s s' : State f} -> (t t' : Term ty) -> Step s t s' t' -> ty == ty
preservation t t' step = refl

-- Reducible terms
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : forall {f : TypeEnv} {s s' : State f} {t' : Term ty} -> Step s t s' t' -> Red t

-- Normal forms, i.e. irreducible terms
NF : ∀ {ty} -> Term ty → Set
NF t = Not (Red t)

-- Evidence type that shows a certain term represents a value.
data Is-value {ty : Type} : Term ty -> Set where
  is-value : forall v -> Is-value ⌜ v ⌝

toVal : forall {ty} -> (t : Term ty) -> Is-value t -> Value ty
toVal .(⌜ v ⌝) (is-value v) = v


--------------------------------------------------------------------------------
-------------------------  Sequences of small steps  ---------------------------
--------------------------------------------------------------------------------

-- A sequence of steps that can be applied in succession
data Steps {ty : Type} {f : TypeEnv} : State f -> Term ty -> State f -> Term ty -> Set where
  Nil : forall {s t} -> Steps s t s t
  Cons : forall {s1 s2 s3 t1 t2 t3} -> Step s1 t1 s2 t2 -> Steps s2 t2 s3 t3 -> Steps s1 t1 s3 t3

-- Single-step sequence
[_] : forall {ty : Type} {f : TypeEnv} {s1 s2 : State f} {t1 t2 : Term ty} -> Step s1 t1 s2 t2 -> Steps s1 t1 s2 t2
[_] x = Cons x Nil
  
-- Concatenation.
_++_ : forall {ty : Type} {f : TypeEnv} {s1 s2 s3 : State f} {t1 t2 t3 : Term ty} -> Steps s1 t1 s2 t2 -> Steps s2 t2 s3 t3 -> Steps s1 t1 s3 t3
Nil ++ stps' = stps'
Cons x stps ++ stps' = Cons x (stps ++ stps')

infixr 5 _++_

