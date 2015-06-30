module SmallStepSemantics.Step where

open import Lib
open import State
open import Definitions

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
  E-Ref : {typeOf : TypeEnv} {s : State typeOf} {ty : Type} {t t' : Term ty} {s' : State (allocType ty (getPointerLimit s) typeOf)} {t' : Term (POINTER ty)} -> Is-value t -> s' == (snd (alloc t s)) -> t' == (fst (alloc t s)) -> Step s (ref t) s' t'
  -- We must first evaluate the expression to normal form before we can dereference it
  E-Ref-Fst : {typeOf : TypeEnv} {s s' : State typeOf} {ty : Type} {t t' : Term (POINTER ty)} -> Step s t s' t' -> Step s (ref t) s' (ref t')
  -- 

values-do-not-step : forall {ty : Type} {f f' : TypeEnv} {s1 : State f} {s2 : State f'} -> (v : Value ty) (t : Term ty) -> Step s1 ⌜ v ⌝  s2 t -> Empty
values-do-not-step vtrue t ()
values-do-not-step vfalse t ()
values-do-not-step (vnat x) t step = lemma x step
  where
  lemma : forall {f f' : TypeEnv} {s : State f} {s' : State f'} -> (n : Nat) -> {t : Term NAT} -> Step s (natTerm n) s' t -> Empty
  lemma Zero ()
  lemma (Succ n) (E-Succ step) = lemma n step
values-do-not-step (vvar n) t ()
values-do-not-step vnothing t ()

is-value-does-not-step : forall {ty : Type} {f f' : TypeEnv} {s1 : State f} {s2 : State f'} -> (t t' : Term ty) -> Is-value t -> Step s1 t s2 t' -> Empty
is-value-does-not-step .true t' (is-value vtrue) ()
is-value-does-not-step .false t' (is-value vfalse) ()
is-value-does-not-step .zero t' (is-value (vnat Zero)) ()
is-value-does-not-step .(succ (natTerm x)) ._ (is-value (vnat (Succ x))) (E-Succ s) = is-value-does-not-step (natTerm x) _ (is-value (vnat x)) s
is-value-does-not-step .(var x) t' (is-value (vvar x)) ()
is-value-does-not-step .<> t' (is-value vnothing) ()

-- Reducible terms
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : forall {f : TypeEnv} {s s' : State f} {t' : Term ty} -> Step s t s' t' -> Red t

-- Normal forms, i.e. irreducible terms
NF : ∀ {ty} -> Term ty → Set
NF t = Not (Red t)

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
