module SmallStepSemantics where

open import State
open import Definitions
open import Lib

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

deterministic-TypeEnv : forall {ty} {f f' f'' : TypeEnv} {s : State f}{s' : State f'}{s'' : State f''} {t t' t'' : Term ty} -> Step s t s' t' -> Step s t s'' t'' → f' == f''
deterministic-TypeEnv {t = true} () s2
deterministic-TypeEnv {t = false} () s2
deterministic-TypeEnv {t = if .true then t₁ else t₂} E-If-True E-If-True = refl
deterministic-TypeEnv {t = if .true then t₁ else t₂} E-If-True (E-If-If ())
deterministic-TypeEnv {t = if .false then t₁ else t₂} E-If-False E-If-False = refl
deterministic-TypeEnv {t = if .false then t₁ else t₂} E-If-False (E-If-If ())
deterministic-TypeEnv {t = if .true then t₁ else t₂} (E-If-If ()) E-If-True
deterministic-TypeEnv {t = if .false then t₁ else t₂} (E-If-If ()) E-If-False
deterministic-TypeEnv {t = if t then t₁ else t₂} (E-If-If s1) (E-If-If s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = zero} () s2
deterministic-TypeEnv {t = succ t} (E-Succ s1) (E-Succ s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = iszero .zero} E-IsZeroZero E-IsZeroZero = refl
deterministic-TypeEnv {t = iszero .zero} E-IsZeroZero (E-IsZero ())
deterministic-TypeEnv {t = iszero (succ x)} E-IsZeroSucc E-IsZeroSucc = refl
deterministic-TypeEnv {t = iszero (succ x)} E-IsZeroSucc (E-IsZero (E-Succ s2)) = refl
deterministic-TypeEnv {t = iszero .zero} (E-IsZero ()) E-IsZeroZero
deterministic-TypeEnv {t = iszero (succ x)} (E-IsZero (E-Succ s1)) (E-IsZeroSucc) = refl
deterministic-TypeEnv {t = iszero t} (E-IsZero s1) (E-IsZero s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = var x} () s2
deterministic-TypeEnv {t = ref t} (E-Ref isv₁ st₁ refl) (E-Ref isv₂ st₂ refl) = refl
deterministic-TypeEnv {t = ref t} (E-Ref isv₁ st₁ refl) (E-Ref-Fst s2) = contradiction (is-value-does-not-step t _ isv₁ s2)
deterministic-TypeEnv {t = ref t} (E-Ref-Fst s1) (E-Ref isv₂ st refl) = contradiction (is-value-does-not-step t _ isv₂ s1)
deterministic-TypeEnv {t = ref t} (E-Ref-Fst s1) (E-Ref-Fst s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = ._ => ._} (E-=> r r') (E-=> r₁ r'') = refl
deterministic-TypeEnv {t = ._ => ._} (E-=> r r') (E-=>-Fst ())
deterministic-TypeEnv {t = ._ => ._} (E-=> r r') (E-=>-Snd ())
deterministic-TypeEnv {t = ._ => ._} (E-=>-Fst ()) (E-=> r r')
deterministic-TypeEnv {t = ._ => ._} (E-=>-Fst s1) (E-=>-Fst s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = ._ => ._} (E-=>-Fst ()) (E-=>-Snd s2)
deterministic-TypeEnv {t = ._ => ._} (E-=>-Snd ()) (E-=> r r')
deterministic-TypeEnv {t = ._ => ._} (E-=>-Snd s1) (E-=>-Fst ())
deterministic-TypeEnv {t = ._ => ._} (E-=>-Snd s1) (E-=>-Snd s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = ._ := ._} (E-:= r) (E-:= r₁) = refl
deterministic-TypeEnv {t = ._ := ._} (E-:= r) (E-:=-Fst ())
deterministic-TypeEnv {t = ._ := ._} (E-:=-Fst ()) (E-:= r)
deterministic-TypeEnv {t = ._ := ._} (E-:=-Fst s1) (E-:=-Fst s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = .<> % ._} E-% E-% = refl
deterministic-TypeEnv {t = .<> % ._} E-% (È-%-Fst ())
deterministic-TypeEnv {t = .<> % ._} (È-%-Fst ()) E-%
deterministic-TypeEnv {t = ._ % ._} (È-%-Fst s1) (È-%-Fst s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = ! ._} E-! E-! = refl
deterministic-TypeEnv {t = ! ._} E-! (E-!-Fst ())
deterministic-TypeEnv {t = ! ._} (E-!-Fst s1) E-! = refl
deterministic-TypeEnv {t = ! ._} (E-!-Fst s1) (E-!-Fst s2) = deterministic-TypeEnv s1 s2
deterministic-TypeEnv {t = <>} () s2

-- Proving the small step semantics are deterministic
deterministic-term : forall {ty} {f f' f'' : TypeEnv} {s : State f}{s' : State f'}{s'' : State f''} {t t' t'' : Term ty} -> Step s t s' t' -> Step s t s'' t'' → t' == t''
deterministic-term {t = true} ()
deterministic-term {t = false} ()
deterministic-term {t = if .true then t₁ else t₂} E-If-True E-If-True = refl
deterministic-term {t = if .true then t₁ else t₂} E-If-True (E-If-If ())
deterministic-term {t = if .false then t₁ else t₂} E-If-False E-If-False = refl
deterministic-term {t = if .false then t₁ else t₂} E-If-False (E-If-If ())
deterministic-term {t = if .true then t₁ else t₂} (E-If-If ()) E-If-True
deterministic-term {t = if .false then t₁ else t₂} (E-If-If ()) E-If-False
deterministic-term {t = if t then t₁ else t₂} (E-If-If s1) (E-If-If s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = zero} ()
deterministic-term {t = succ t} (E-Succ s1) (E-Succ s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = iszero .zero} E-IsZeroZero E-IsZeroZero = refl
deterministic-term {t = iszero .zero} E-IsZeroZero (E-IsZero ())
deterministic-term {t = iszero ._} E-IsZeroSucc E-IsZeroSucc = refl
deterministic-term {t = iszero .(succ ⌜ v ⌝)} (E-IsZeroSucc {isv = is-value v}) (E-IsZero (E-Succ s2)) = contradiction (values-do-not-step v _ s2)
deterministic-term {t = iszero .zero} (E-IsZero ()) E-IsZeroZero
deterministic-term {t = iszero .(succ ⌜ v ⌝)} (E-IsZero (E-Succ s1)) (E-IsZeroSucc {isv = is-value v}) = contradiction (values-do-not-step v _ s1)
deterministic-term {t = iszero t} (E-IsZero s1) (E-IsZero s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = var x} ()
deterministic-term {t = ref t} (E-Ref isv₁ steq₁ refl) (E-Ref isv₂ steq₂ refl) = refl
deterministic-term {t = ref t} (E-Ref isv₁ steq₁ refl) (E-Ref-Fst s2) = contradiction (is-value-does-not-step t _ isv₁ s2)
deterministic-term {t = ref t} (E-Ref-Fst s1) (E-Ref isv₂ steq₂ refl) = contradiction (is-value-does-not-step t _ isv₂ s1)
deterministic-term {t = ref t} (E-Ref-Fst s1) (E-Ref-Fst s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = ._ => ._} (E-=> r r') (E-=> r₁ r'') = refl
deterministic-term {t = ._ => ._} (E-=> r r') (E-=>-Fst ())
deterministic-term {t = ._ => ._} (E-=> r r') (E-=>-Snd ())
deterministic-term {t = ._ => ._} (E-=>-Fst ()) (E-=> r r')
deterministic-term {t = ._ => ._} (E-=>-Fst s1) (E-=>-Fst s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = ._ => ._} (E-=>-Fst ()) (E-=>-Snd s2)
deterministic-term {t = ._ => ._} (E-=>-Snd ()) (E-=> r r')
deterministic-term {t = ._ => ._} (E-=>-Snd s1) (E-=>-Fst ())
deterministic-term {t = ._ => ._} (E-=>-Snd s1) (E-=>-Snd s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = ._ := ._} (E-:= r) (E-:= r₁) = refl
deterministic-term {t = ._ := ._} (E-:= r) (E-:=-Fst ())
deterministic-term {t = ._ := ._} (E-:=-Fst ()) (E-:= r)
deterministic-term {t = ._ := ._} (E-:=-Fst s1) (E-:=-Fst s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = .<> % ._} E-% E-% = refl
deterministic-term {t = .<> % ._} E-% (È-%-Fst ())
deterministic-term {t = .<> % ._} (È-%-Fst ()) E-%
deterministic-term {t = ._ % ._} (È-%-Fst s1) (È-%-Fst s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = ! ._} E-! E-! = refl
deterministic-term {t = ! ._} E-! (E-!-Fst ())
deterministic-term {t = ! ._} (E-!-Fst ()) E-!
deterministic-term {t = ! ._} (E-!-Fst s1) (E-!-Fst s2) = cong _ (deterministic-term s1 s2)
deterministic-term {t = <>} ()

deterministic-state : forall {ty} {f f' : TypeEnv} {s : State f}{s' : State f'}{s'' : State f'} {t t' t'' : Term ty} -> Step s t s' t' -> Step s t s'' t'' → s' == s''
deterministic-state s1 s2 with deterministic-term s1 s2
deterministic-state {t = true} () _ | _
deterministic-state {t = false} () _ | _
deterministic-state {t = zero} () _ | _
deterministic-state {t = var x} () _ | _
deterministic-state {t = <>} () _ | _
deterministic-state {t = if .true then t₁ else t₂} E-If-True E-If-True | refl = refl
deterministic-state {t = if .false then t₁ else t₂} E-If-False E-If-False | refl = refl
deterministic-state {t = if t then t₁ else t₂} (E-If-If s1) (E-If-If s2) | refl = deterministic-state s1 s2
deterministic-state {t = succ t} (E-Succ s1) (E-Succ s2) | refl = deterministic-state s1 s2
deterministic-state {t = iszero .zero} E-IsZeroZero E-IsZeroZero | refl = refl
deterministic-state {t = iszero ._} E-IsZeroSucc E-IsZeroSucc | refl = refl
deterministic-state {t = iszero t} (E-IsZero s1) (E-IsZero s2) | refl = deterministic-state s1 s2
--                   t = ref t
deterministic-state {._} {f} {._} {state .f pointerLimit x} {state ._ .pointerLimit ._} {._} {ref .(⌜ v ⌝)} (E-Ref (is-value v) refl refl) (E-Ref x₁ refl refl) | refl = refl
deterministic-state {._} {f} {.f} {state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {ref t} {._} {if t'' then t''' else t''''} (E-Ref-Fst s1) s2 | ()
deterministic-state {._} {f} {.f} {state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {ref t} {._} {var x₃} (E-Ref-Fst s1) s2 | ()
deterministic-state {POINTER (POINTER ty)} {f} {.f} {s}{s'}{s''} {t = ref t''} {(ref t2)} {ref t3} (E-Ref-Fst s1) s2 | r = lemma s2 refl s1 where
    lemma : ∀{tyₗ f f' tₗ'''} {s : State f}{ s' s'' : State f'} {tₗ'' : Term tyₗ}{t3 : Term (POINTER tyₗ)} -> Step s (ref tₗ'') s'' t3 -> tyₗ == (POINTER ty) -> Step {f = f} {f' = f'} s tₗ'' s' tₗ''' -> s' == s''
    lemma {tₗ''' = tₗ'''} {tₗ'' = tₗ''} (E-Ref v refl refl) refl s1ₗ = contradiction (is-value-does-not-step tₗ'' tₗ''' v s1ₗ)
    lemma (E-Ref-Fst s3) refl s = deterministic-state s s3
deterministic-state {POINTER (POINTER ty)} {f} {.f} {s} {s'} {s''} {ref t''} {._} { ! t'''} (E-Ref-Fst s1) s2 | ()

deterministic-state {f = f} {s = state .f pointerLimit x} {state .f .pointerLimit ._} {state .f .pointerLimit ._} {._ => ._} (E-=> r refl) (E-=> r₁ refl) | refl with proof-irrelevance {_}{_}{_} {r} {r₁}
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f .pointerLimit ._} {state .f .pointerLimit ._} {t = ._ => ._} (E-=> r refl) (E-=> .r refl) | refl | refl = refl
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f .pointerLimit ._} {state .f pointerLimit₂ x₂} {._ => ._} (E-=> r r') (E-=>-Fst ()) | _
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f .pointerLimit ._} {state .f pointerLimit₂ x₂} {._ => ._} (E-=> r r') (E-=>-Snd ()) | _
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f .pointerLimit ._} {._ => ._} (E-=>-Fst ()) (E-=> r r') | _
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {x₃ => x₄} (E-=>-Fst s1) (E-=>-Fst s2) | _ = deterministic-state s1 s2
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {._ => x₄} (E-=>-Fst ()) (E-=>-Snd s2) | _
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f .pointerLimit ._} {._ => ._} (E-=>-Snd ()) (E-=> r r') | _
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {._ => x₄} (E-=>-Snd s1) (E-=>-Fst ()) | _
deterministic-state {f = f} {s = state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {._ => x₄} (E-=>-Snd s1) (E-=>-Snd s2) | _ = deterministic-state s1 s2
deterministic-state {t = ._ := t₁} (E-:= refl) (E-:= refl) | refl = refl
deterministic-state {t = ._ := t₁} (E-:=-Fst s1) (E-:=-Fst s2) | refl = deterministic-state s1 s2
deterministic-state {t = .<> % t₁} E-% E-% | refl = refl
deterministic-state {t = t % t₁} (È-%-Fst s1) (È-%-Fst s2) | refl = deterministic-state s1 s2
deterministic-state {t = ! ._} E-! E-! | _ = refl
deterministic-state {t = ! ._} E-! (E-!-Fst ()) | _
deterministic-state {t = ! ._} (E-!-Fst ()) E-! | _
deterministic-state {t = ! t} (E-!-Fst s1) (E-!-Fst s2) | _ = deterministic-state s1 s2

deterministic-state {t = if .true then t₁ else t₂} E-If-True (E-If-If ()) | _
deterministic-state {t = if .false then t₁ else t₂} E-If-False (E-If-If ()) | _
deterministic-state {t = if .true then t₁ else t₂} (E-If-If ()) E-If-True | _
deterministic-state {t = if .false then t₁ else t₂} (E-If-If ()) E-If-False | _
deterministic-state {t = iszero .zero} E-IsZeroZero (E-IsZero ()) | _
deterministic-state {t = iszero ._} E-IsZeroSucc (E-IsZero (E-Succ _)) | ()
deterministic-state {t = iszero .zero} (E-IsZero ()) E-IsZeroZero | _
deterministic-state {t = iszero ._} (E-IsZero (E-Succ _)) E-IsZeroSucc | ()
deterministic-state {t = ._ := t₁} (E-:= r) (E-:=-Fst ()) | _
deterministic-state {t = ._ := t₁} (E-:=-Fst ()) (E-:= r) | _
deterministic-state {t = .<> % t₁} E-% (È-%-Fst ()) | _
deterministic-state {t = .<> % t₁} (È-%-Fst ()) E-% | _

-- Types are preserved during evaluation
preservation : forall {ty : Type} {f : TypeEnv} {s s' : State f} -> (t t' : Term ty) -> Step s t s' t' -> ty == ty
preservation t t' step = refl

-- Reducible terms
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : forall {f : TypeEnv} {s s' : State f} {t' : Term ty} -> Step s t s' t' -> Red t

-- Normal forms, i.e. irreducible terms
NF : ∀ {ty} -> Term ty → Set
NF t = Not (Red t)
