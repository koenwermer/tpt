module SmallStepSemantics.Deterministic where

open import State
open import Definitions
open import Lib
open import SmallStepSemantics.Step

-- Proving the small step semantics are deterministic
-- Three proofs are given, for the term, type environment and state

-- Each possible step results in the same type environment
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

-- Each possible step results in the same term
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

-- Each possible step results in the same state
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

-- cases for         t = ref t
deterministic-state {._} {f} {._} {state .f pointerLimit x} {state ._ .pointerLimit ._} {._} {ref .(⌜ v ⌝)} (E-Ref (is-value v) refl refl) (E-Ref x₁ refl refl) | refl = refl
deterministic-state {._} {f} {.f} {state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {ref t} {._} {if t'' then t''' else t''''} (E-Ref-Fst s1) s2 | ()
deterministic-state {._} {f} {.f} {state .f pointerLimit x} {state .f pointerLimit₁ x₁} {state .f pointerLimit₂ x₂} {ref t} {._} {var x₃} (E-Ref-Fst s1) s2 | ()
deterministic-state {POINTER (POINTER ty)} {f} {.f} {s}{s'}{s''} {t = ref t''} {(ref t2)} {ref t3} (E-Ref-Fst s1) s2 | r = lemma s2 refl s1 where
    lemma : ∀{tyₗ f f' tₗ'''} {s : State f}{ s' s'' : State f'} {tₗ'' : Term tyₗ}{t3 : Term (POINTER tyₗ)} -> Step s (ref tₗ'') s'' t3 -> tyₗ == (POINTER ty) -> Step {f = f} {f' = f'} s tₗ'' s' tₗ''' -> s' == s''
    lemma {tₗ''' = tₗ'''} {tₗ'' = tₗ''} (E-Ref v refl refl) refl s1ₗ = contradiction (is-value-does-not-step tₗ'' tₗ''' v s1ₗ)
    lemma (E-Ref-Fst s3) refl s = deterministic-state s s3
deterministic-state {POINTER (POINTER ty)} {f} {.f} {s} {s'} {s''} {ref t''} {._} { ! t'''} (E-Ref-Fst s1) s2 | ()

-- cases for         t = _ => _    (pointer assignment)
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
