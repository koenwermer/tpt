
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
  ref           : {ty : Type} -> Term ty -> Term (POINTER ty)

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
  state : (f : TypeEnv) -> (pointerLimit : Pointer) -> ((p : Pointer) -> (Term (f p))) -> State f

-- The types of values that will be stored can of course not be known beforehand,
-- therefore we proof that we have an initial state that is valid for every possible typing
-- Of course we can't get values from empty cells, so we just recurse
-- (In practice, getting an error would be prefered over your program getting stuck in a loop, but for this project it doesn't matter)
initState : forall {f} -> State f
initState {f} = state f Zero (λ p -> ! (var p))

-- Some usefull functions on state:
-- Retrieves the values of a given pointer from the state, and rewrites the type using equational reasoning
getEq : {typeOf : TypeEnv} {ty : Type} -> State typeOf -> (n : Pointer) -> typeOf n == ty -> Term ty
getEq {typeOf} (state .typeOf _ env) n refl = env n

-- Redirects a pointer to another cell
redirect : {typeOf : TypeEnv} -> (n : Pointer) -> (m : Pointer) -> typeOf n == typeOf m -> State typeOf -> State typeOf
redirect n m r (state typeOf pointerLimit env) = state typeOf pointerLimit env'
  where
  env' : (p : Pointer) -> (Term (typeOf p))
  env' p with p `eq` n
  env' p | Left t with trans (cong typeOf t) r
  env' .n | Left refl | y = getEq (state typeOf pointerLimit env) m (symm y)
  env' p | Right _ = env p

-- Stores an expression in a cell
store : {ty : Type} {typeOf : TypeEnv} -> (n : Pointer) -> (t : Term ty) -> typeOf n == ty -> State typeOf -> State typeOf
store n t refl (state typeOf pointerLimit env) = state typeOf pointerLimit env'
  where
  env' : (p : Pointer) -> (Term (typeOf p))
  env' p with p `eq` n
  env' .n | Left refl = t
  env' p | Right _ = env p

allocType : Type -> Pointer -> TypeEnv -> TypeEnv
allocType ty maxPointer tyEnv p with p `eq` maxPointer
allocType ty maxPointer tyEnv .maxPointer | Left refl = ty
allocType ty maxPointer tyEnv p | Right x = tyEnv p

getPointerLimit : ∀ {typeEnv} -> State typeEnv -> Pointer
getPointerLimit (state _ pointerLimit _) = pointerLimit

alloc : {ty : Type} {typeOf : TypeEnv} -> (t : Term ty) -> (s : State typeOf) -> Tuple (Term (POINTER ty)) (State (allocType ty (getPointerLimit s) typeOf))
alloc {ty} t (state typeOf pointerLimit env) = var this , state (allocType ty pointerLimit typeOf) pointerLimit env'
  where
  this = pointerLimit
  pointerLimit' = Succ this
  typeOf' : TypeEnv
  typeOf' p with p `eq` this
  typeOf' ._ | Left refl = ty
  typeOf' p | Right _ = typeOf p
  env' : (p : Pointer) -> (Term ((allocType ty this typeOf) p))
  env' p with p `eq` this
  env' ._ | Left refl = ! var this
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

-- Evidence type that shows a certain term represents a value.
data Is-value {ty : Type} : Term ty -> Set where
  is-value : forall v -> Is-value ⌜ v ⌝

toVal : forall {ty} -> (t : Term ty) -> Is-value t -> Value ty
toVal .(⌜ v ⌝) (is-value v) = v


-------------------------------------------------------------------------------
----------------------             Small-step            ----------------------
-------------------------------------------------------------------------------

data Step  : {ty : Type} {f f' : TypeEnv} -> State f -> Term ty → State f' -> Term ty → Set where
  -- Pure thingies leave the state unchanged, but may contain non-pure expressions and propagate the changes made by those
  E-If-True : {f : TypeEnv} {s : State f} {ty : Type} {t1 t2 : Term ty} -> Step s (if true then t1 else t2) s t1
  E-If-False : {f : TypeEnv} {s : State f} {ty : Type} {t1 t2 : Term ty} -> Step s (if false then t1 else t2) s t2
  E-If-If : {f : TypeEnv} {s s' : State f} {ty : Type} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step s t1 s' t1' -> 
    Step s (if t1 then t2 else t3) s' (if t1' then t2 else t3)
  E-Succ       : {f : TypeEnv} {s s' : State f} {t t' : Term NAT} -> Step {NAT} s t s' t' -> Step {NAT} s (succ t) s' (succ t')
  E-IsZeroZero : {f : TypeEnv} {s : State f} -> Step s (iszero zero) s true
  E-IsZeroSucc : {f : TypeEnv} {s : State f} {vt : Term NAT}{isv : Is-value vt} -> Step s (iszero (succ vt)) s false
  E-IsZero     : {f f' : TypeEnv} {s : State f} {s' : State f'} {t t' : Term NAT} -> Step s t s' t' -> Step s (iszero t) s' (iszero t')
  -- Pointer thingies may use or change the state
  -- We can redirect pointers to other cells iff the the types match. Both arguments of => must be completely evaluated
  E-=> : {typeOf : TypeEnv} {s : State typeOf} {ty : Type} {n m : Nat} -> (r : typeOf n == ty) (r' : typeOf m == ty) -> Step s (_=>_ {ty} (var n) (var m)) (redirect n m (trans r (symm r')) s) <>
  -- We first evaluate the first argument of => to a pointer
  E-=>-Fst : {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t1 t1' t2 : Term (POINTER ty)} -> Step s t1 s' t1' -> Step s (t1 => t2) s' (t1' => t2)
  -- If the first argument is a pointer, we evaluate the second argument
  E-=>-Snd : {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {n : Nat} {t2 t2' : Term (POINTER ty)} -> Step s t2 s' t2' -> Step s (var n => t2) s' (var n => t2')
  -- We can store any expression in a cell, as long as the types match
  E-:= : {typeOf : TypeEnv} {s : State typeOf} {ty : Type} {n : Nat} {t : Term ty} -> (r : typeOf n == ty) -> Step s (_:=_ {ty} (var n) t) (store n t r s) <>
  -- We must first evaluate the first argument of := to a pointer
  E-:=-Fst : {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t1 t1' : Term (POINTER ty)} {t2 : Term ty} -> Step s t1 s' t1' -> Step s (t1 := t2) s' (t1' := t2)
  -- We can eliminate sequencing only if the first argument if completely evaluated
  E-% : {typeOf : TypeEnv} {s : State typeOf} {t : Term <>} -> Step s (<> % t) s t
  -- Of course, sequencing evaluates the first argument first
  È-%-Fst : {typeOf : TypeEnv} {s s' : State typeOf} {t1 t1' t2 : Term <>} -> Step s t1 s' t1' -> Step s (t1 % t2) s' (t1' % t2)
  -- Dereferencing just gets the stored expression from the state
  E-! : {typeOf : TypeEnv} {s : State typeOf} {n : Nat} -> Step s (! (var n)) s (get s n)
  -- We must first evaluate the pointer expression to normal form before we can dereference it
  E-!-Fst : {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t t' : Term (POINTER ty)} -> Step s t s' t' -> Step s (! t) s' (! t')
  -- Allocating just puts the given expression in the state
  E-Ref : {typeOf : TypeEnv} {s : State typeOf} {ty : Type} {t : Term ty} {n : Nat} {s' : State (allocType ty (getPointerLimit s) typeOf)} {t' : Term (POINTER ty)} -> s' == (snd (alloc t s)) -> t' == (fst (alloc t s)) -> Is-value t ->  Step s (ref t) s' (fst (alloc t s))
  -- We must first evaluate the expression to normal form before we can dereference it
  E-Ref-Fst : {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t t' : Term (POINTER ty)} -> Step s t s' t' -> Step s (ref t) s' (ref t')
  -- 

valuesDoNotStep : forall {ty : Type} {f f' : TypeEnv} {s1 : State f} {s2 : State f'} -> (v : Value ty) (t : Term ty) -> Step s1 ⌜ v ⌝  s2 t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x step
  where
  lemma : forall {f f' : TypeEnv} {s : State f} {s' : State f'} -> (n : Nat) -> {t : Term NAT} -> Step s (natTerm n) s' t -> Empty
  lemma Zero ()
  lemma (Succ n) (E-Succ step) = lemma n step
valuesDoNotStep (vvar n) t ()
valuesDoNotStep vnothing t ()

is-valueDoesNotStep : forall {ty : Type} {f f' : TypeEnv} {s1 : State f} {s2 : State f'} -> (t t' : Term ty) -> Is-value t -> Step s1 t s2 t' -> Empty
is-valueDoesNotStep .true t' (is-value vtrue) ()
is-valueDoesNotStep .false t' (is-value vfalse) ()
is-valueDoesNotStep .zero t' (is-value (vnat Zero)) ()
is-valueDoesNotStep .(succ (natTerm x)) ._ (is-value (vnat (Succ x))) (E-Succ s) = is-valueDoesNotStep (natTerm x) _ (is-value (vnat x)) s
is-valueDoesNotStep .(var x) t' (is-value (vvar x)) ()
is-valueDoesNotStep .<> t' (is-value vnothing) ()

deterministicTypeEnv : forall {ty} {f f' f'' : TypeEnv} {s : State f}{s' : State f'}{s'' : State f''} {t t' t'' : Term ty} -> Step s t s' t' -> Step s t s'' t'' → f' == f''
deterministicTypeEnv {t = true} () s2
deterministicTypeEnv {t = false} () s2
deterministicTypeEnv {t = if .true then t₁ else t₂} E-If-True E-If-True = refl
deterministicTypeEnv {t = if .true then t₁ else t₂} E-If-True (E-If-If ())
deterministicTypeEnv {t = if .false then t₁ else t₂} E-If-False E-If-False = refl
deterministicTypeEnv {t = if .false then t₁ else t₂} E-If-False (E-If-If ())
deterministicTypeEnv {t = if .true then t₁ else t₂} (E-If-If ()) E-If-True
deterministicTypeEnv {t = if .false then t₁ else t₂} (E-If-If ()) E-If-False
deterministicTypeEnv {t = if t then t₁ else t₂} (E-If-If s1) (E-If-If s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = zero} () s2
deterministicTypeEnv {t = succ t} (E-Succ s1) (E-Succ s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = iszero .zero} E-IsZeroZero E-IsZeroZero = refl
deterministicTypeEnv {t = iszero .zero} E-IsZeroZero (E-IsZero ())
deterministicTypeEnv {t = iszero (succ x)} E-IsZeroSucc E-IsZeroSucc = refl
deterministicTypeEnv {t = iszero (succ x)} E-IsZeroSucc (E-IsZero (E-Succ s2)) = refl
deterministicTypeEnv {t = iszero .zero} (E-IsZero ()) E-IsZeroZero
deterministicTypeEnv {t = iszero (succ x)} (E-IsZero (E-Succ s1)) (E-IsZeroSucc) = refl
deterministicTypeEnv {t = iszero t} (E-IsZero s1) (E-IsZero s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = var x} () s2
deterministicTypeEnv {t = ref t} (E-Ref x x₁ x₂) (E-Ref x₃ x₄ x₅) = refl
deterministicTypeEnv {t = ref t} (E-Ref x x₁ x₂) (E-Ref-Fst s2) = contradiction (is-valueDoesNotStep t _ x₂ s2)
deterministicTypeEnv {t = ref t} (E-Ref-Fst s1) (E-Ref x x₁ x₂) = contradiction (is-valueDoesNotStep t _ x₂ s1)
deterministicTypeEnv {t = ref t} (E-Ref-Fst s1) (E-Ref-Fst s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = ._ => ._} (E-=> r r') (E-=> r₁ r'') = refl
deterministicTypeEnv {t = ._ => ._} (E-=> r r') (E-=>-Fst ())
deterministicTypeEnv {t = ._ => ._} (E-=> r r') (E-=>-Snd ())
deterministicTypeEnv {t = ._ => ._} (E-=>-Fst ()) (E-=> r r')
deterministicTypeEnv {t = ._ => ._} (E-=>-Fst s1) (E-=>-Fst s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = ._ => ._} (E-=>-Fst ()) (E-=>-Snd s2)
deterministicTypeEnv {t = ._ => ._} (E-=>-Snd ()) (E-=> r r')
deterministicTypeEnv {t = ._ => ._} (E-=>-Snd s1) (E-=>-Fst ())
deterministicTypeEnv {t = ._ => ._} (E-=>-Snd s1) (E-=>-Snd s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = ._ := ._} (E-:= r) (E-:= r₁) = refl
deterministicTypeEnv {t = ._ := ._} (E-:= r) (E-:=-Fst ())
deterministicTypeEnv {t = ._ := ._} (E-:=-Fst ()) (E-:= r)
deterministicTypeEnv {t = ._ := ._} (E-:=-Fst s1) (E-:=-Fst s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = .<> % ._} E-% E-% = refl
deterministicTypeEnv {t = .<> % ._} E-% (È-%-Fst ())
deterministicTypeEnv {t = .<> % ._} (È-%-Fst ()) E-%
deterministicTypeEnv {t = ._ % ._} (È-%-Fst s1) (È-%-Fst s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = ! ._} E-! E-! = refl
deterministicTypeEnv {t = ! ._} E-! (E-!-Fst ())
deterministicTypeEnv {t = ! ._} (E-!-Fst s1) E-! = refl
deterministicTypeEnv {t = ! ._} (E-!-Fst s1) (E-!-Fst s2) = deterministicTypeEnv s1 s2
deterministicTypeEnv {t = <>} () s2

-- Proving the small step semantics are deterministic
deterministic : forall {ty} {f f' f'' : TypeEnv} {s : State f}{s' : State f'}{s'' : State f''} {t t' t'' : Term ty} -> Step s t s' t' -> Step s t s'' t'' → t' == t''
deterministic {t = true} ()
deterministic {t = false} ()
deterministic {t = if .true then t₁ else t₂} E-If-True E-If-True = refl
deterministic {t = if .true then t₁ else t₂} E-If-True (E-If-If ())
deterministic {t = if .false then t₁ else t₂} E-If-False E-If-False = refl
deterministic {t = if .false then t₁ else t₂} E-If-False (E-If-If ())
deterministic {t = if .true then t₁ else t₂} (E-If-If ()) E-If-True
deterministic {t = if .false then t₁ else t₂} (E-If-If ()) E-If-False
deterministic {t = if t then t₁ else t₂} (E-If-If s1) (E-If-If s2) = cong _ (deterministic s1 s2)
deterministic {t = zero} ()
deterministic {t = succ t} (E-Succ s1) (E-Succ s2) = cong _ (deterministic s1 s2)
deterministic {t = iszero .zero} E-IsZeroZero E-IsZeroZero = refl
deterministic {t = iszero .zero} E-IsZeroZero (E-IsZero ())
deterministic {t = iszero ._} E-IsZeroSucc E-IsZeroSucc = refl
deterministic {t = iszero .(succ ⌜ v ⌝)} (E-IsZeroSucc {isv = is-value v}) (E-IsZero (E-Succ s2)) = contradiction (valuesDoNotStep v _ s2)
deterministic {t = iszero .zero} (E-IsZero ()) E-IsZeroZero
deterministic {t = iszero .(succ ⌜ v ⌝)} (E-IsZero (E-Succ s1)) (E-IsZeroSucc {isv = is-value v}) = contradiction (valuesDoNotStep v _ s1)
deterministic {t = iszero t} (E-IsZero s1) (E-IsZero s2) = cong _ (deterministic s1 s2)
deterministic {t = var x} ()
deterministic {t = ref t} (E-Ref x x₁ x₂) (E-Ref x₃ x₄ x₅) = refl
deterministic {t = ref t} (E-Ref x x₁ x₂) (E-Ref-Fst s2) = contradiction (is-valueDoesNotStep t _ x₂ s2)
deterministic {t = ref t} (E-Ref-Fst s1) (E-Ref x x₁ x₂) = contradiction (is-valueDoesNotStep t _ x₂ s1)
deterministic {t = ref t} (E-Ref-Fst s1) (E-Ref-Fst s2) = cong _ (deterministic s1 s2)
deterministic {t = ._ => ._} (E-=> r r') (E-=> r₁ r'') = refl
deterministic {t = ._ => ._} (E-=> r r') (E-=>-Fst ())
deterministic {t = ._ => ._} (E-=> r r') (E-=>-Snd ())
deterministic {t = ._ => ._} (E-=>-Fst ()) (E-=> r r')
deterministic {t = ._ => ._} (E-=>-Fst s1) (E-=>-Fst s2) = cong _ (deterministic s1 s2)
deterministic {t = ._ => ._} (E-=>-Fst ()) (E-=>-Snd s2)
deterministic {t = ._ => ._} (E-=>-Snd ()) (E-=> r r')
deterministic {t = ._ => ._} (E-=>-Snd s1) (E-=>-Fst ())
deterministic {t = ._ => ._} (E-=>-Snd s1) (E-=>-Snd s2) = cong _ (deterministic s1 s2)
deterministic {t = ._ := ._} (E-:= r) (E-:= r₁) = refl
deterministic {t = ._ := ._} (E-:= r) (E-:=-Fst ())
deterministic {t = ._ := ._} (E-:=-Fst ()) (E-:= r)
deterministic {t = ._ := ._} (E-:=-Fst s1) (E-:=-Fst s2) = cong _ (deterministic s1 s2)
deterministic {t = .<> % ._} E-% E-% = refl
deterministic {t = .<> % ._} E-% (È-%-Fst ())
deterministic {t = .<> % ._} (È-%-Fst ()) E-%
deterministic {t = ._ % ._} (È-%-Fst s1) (È-%-Fst s2) = cong _ (deterministic s1 s2)
deterministic {t = ! ._} E-! E-! = refl
deterministic {t = ! ._} E-! (E-!-Fst ())
deterministic {t = ! ._} (E-!-Fst ()) E-!
deterministic {t = ! ._} (E-!-Fst s1) (E-!-Fst s2) = cong _ (deterministic s1 s2)
deterministic {t = <>} ()

-- Types are preserved during evaluation
preservation : forall {ty : Type} {f : TypeEnv} {s s' : State f} -> (t t' : Term ty) -> Step s t s' t' -> ty == ty
preservation t t' step = refl

-- Reducible terms
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : forall {f : TypeEnv} {s s' : State f} {t' : Term ty} -> Step s t s' t' -> Red t

-- Normal forms, i.e. irreducible terms
NF : ∀ {ty} -> Term ty → Set
NF t = Not (Red t)


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


--------------------------------------------------------------------------------
-------------------------------  Hoare logic  ----------------------------------
--------------------------------------------------------------------------------

-- A data type for predicates that hold on given state
data Valid : {f : TypeEnv} -> (State f -> Bool) -> State f -> Set where
  P : {f : TypeEnv} -> (p : State f -> Bool) -> (s : State f) -> p s == True -> Valid p s

-- A datatype for valid hoare triples
-- A hoare triple {p}t{q} is valid if s satisfying p implies that s' satisfies q
-- (where s' is the state resulting from completely evaluating the term t)
data HoareTriple : {ty : Type} {f : TypeEnv} -> (State f -> Bool) -> Term ty -> (State f -> Bool) -> Set where
  triple : {ty : Type} {f : TypeEnv} {s s' : State f} {v : Value ty} -> (p : State f -> Bool) -> (t : Term ty) -> (q : State f -> Bool) -> (Steps s t s' ⌜ v ⌝ -> Valid p s -> Valid q s') -> HoareTriple p t q

PreStrengthening : {ty : Type} {f : TypeEnv} {t : Term ty} {p p' q : State f -> Bool} -> HoareTriple p t q -> ({s : State f} -> Valid p' s -> Valid p s) -> HoareTriple p' t q
PreStrengthening {ty} {f} {t} {p} {p'} {q} (triple {.ty} {.f} {s} {s'} {v} .p .t .q y) g = triple {ty} {f} {s} {s'} {v} p' t q (λ steps valid -> y steps (g valid))

PostWeakening : {ty : Type} {f : TypeEnv} {t : Term ty} {p q q' : State f -> Bool} -> HoareTriple p t q -> ({s : State f} -> Valid q s -> Valid q' s) -> HoareTriple p t q'
PostWeakening {ty} {f} {t} {p} {q} {q'} (triple {.ty} {.f} {s} {s'} {v} .p .t .q y) g = triple {ty} {f} {s} {s'} {v} p t q' (λ steps valid -> g (y steps valid))

-- The hoare rule for sequencing side effects
Sequencing : {f : TypeEnv} {t1 t2 : Term <>} {p q r : State f -> Bool} -> HoareTriple p t1 q -> HoareTriple q t2 r -> HoareTriple p (t1 % t2) r
Sequencing {f} {t1} {t2} {p} {q} {r} (triple {.<>} {.f} {s} {s'} .p .t1 .q y) (triple {.<>} {.f} .q .t2 .r y') = triple p (t1 % t2) r y''
  where
  y'' : {s s' : State f} {t1 t2 : Term <>} -> Steps s (t1 % t2) s' <> -> Valid p s -> Valid r s
  y'' (Cons E-% y1) v = {!!}
  y'' (Cons (È-%-Fst y0) y1) v = {!!}
