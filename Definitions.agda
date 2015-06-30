module Definitions where

open import Lib

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

Pointer = Nat

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
  var           : {ty : Type} -> Pointer -> Term (POINTER ty)

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
TypeEnv = Pointer -> Type

-- The environment returns the actual expressions, and is given a type environment that matches the expressions
-- The state consists of a matching environment and type environment
data State : TypeEnv -> Set where
  state : (f : TypeEnv) -> (pointerLimit : Pointer) -> ((p : Pointer) -> (Term (f p))) -> State f

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

