
module Project where

-------------------------------------------------------------------------------
----------------------  Prelude - copied from exercise 2a  --------------------
-------------------------------------------------------------------------------

-- Equality.
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  
cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f refl = refl

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
  -- Pointer shit
  -- Create a new cell with an initial value
  ref           : {ty : Type} -> Term ty -> Term (POINTER ty)
  -- Redirecting a pointer to another cell, similar to "=" in the book
  _=>_           : {ty : Type} -> Term (POINTER ty) -> Term (POINTER ty) -> Term <>
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

-- And of course the state itself..
State = (f : TypeEnv) -> (p : Pointer) -> Term (f p)


-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  vnat : Nat -> Value NAT
  vref : {ty : Type} -> Value ty -> Value (POINTER ty)
  vnothing : Value <>

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat k ⌝ = natTerm k
⌜ vref v ⌝ = ref ⌜ v ⌝
⌜ vnothing ⌝ = <>

-------------------------------------------------------------------------------
----------------------            Denotational           ----------------------
-------------------------------------------------------------------------------

cond : forall {ty} -> Value BOOL → Value ty → Value ty → Value ty
cond vtrue v2 v3 = v2
cond vfalse v2 v3 = v3

vsucc : Value NAT -> Value NAT
vsucc (vnat x) = vnat (Succ x)

viszero : Value NAT -> Value BOOL
viszero (vnat Zero) = vtrue
viszero (vnat (Succ x)) = vfalse

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ t ⟧ = {!!}

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data Step  : {ty : Type} ->  State -> Term ty → State -> Term ty → Set where
  -- Pure thingies leave the state unchanged, but may contain non-pure expressions and propagate the changes made by those
  E-If-True : forall {s : State} {ty} {t1 t2 : Term ty} -> Step s (if true then t1 else t2) s t1
  E-If-False : forall {s : State} {ty} {t1 t2 : Term ty} -> Step s (if false then t1 else t2) s t2
  E-If-If : forall {s s' : State} {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step s t1 s' t1' -> 
    Step s (if t1 then t2 else t3) s' (if t1' then t2 else t3)
  E-Succ       : {s s' : State} {t t' : Term NAT} -> Step {NAT} s t s' t' -> Step {NAT} s (succ t) s' (succ t')
  E-IsZeroZero : {s : State} -> Step s (iszero zero) s true
  E-IsZeroSucc : {s : State} {v : Value NAT} -> Step s (iszero (succ ⌜ v ⌝)) s false
  E-IsZero     : {s s' : State} {t t' : Term NAT} -> Step s t s' t' -> Step s (iszero t) s' (iszero t')
  -- Pointer thingies may use or change the state
  E-Ref : forall {s s' : State} {ty : Type} {t t' : Term ty} -> Step s t s' t' -> Step s (ref t) s' (ref t')







valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step _ ⌜ v ⌝  _ t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : {s s' : State} -> (n : Nat) -> (t : Term NAT) -> Step s (natTerm n) s' t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {_} {_} {._} {t} step) = lemma n (t) step
valuesDoNotStep (vref v) t step = {!!}
valuesDoNotStep vnothing t ()





--preservation : forall {ty : Type} -> (t1 t2 : Term ty) -> Step t1 t2 -> ty == ty
--preservation t1 t2 step = refl

-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

-- Evidence type that shows a certain term represents a value.
data Is-value {ty : Type} : Term ty → Set where
  is-value : ∀ v → Is-value ⌜ v ⌝

toVal : forall {ty} -> (t : Term ty) -> Is-value t -> Value ty
toVal .(⌜ v ⌝) (is-value v) = v


--------------------------------------------------------------------------------
-- Sequences of small steps.
--------------------------------------------------------------------------------

-- A sequence of steps that can be applied in succession.
data Steps {ty : Type} : Term ty → Term ty → Set where
  Nil : forall {t} -> Steps t t
  Cons : forall {t1 t2 t3} -> Step t1 t2 -> Steps t2 t3 -> Steps t1 t3

-- Single-step sequence.
[_] : ∀ {ty} {t₁ t₂ : Term ty} -> Step t₁ t₂ -> Steps t₁ t₂
[_] x = Cons x Nil

-- zero steps using equality
trivialSteps : ∀ {ty} {t1 t2 : Term ty} -> t1 == t2 -> Steps t1 t2
trivialSteps refl = Nil
  
-- Concatenation.
_++_ : ∀ {ty} {t₁ t₂ t₃ : Term ty} → Steps t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃
Nil ++ stps' = stps'
Cons x stps ++ stps' = Cons x (stps ++ stps')

infixr 5 _++_