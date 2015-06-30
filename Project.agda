
module Project where

open import Lib
open import State
open import Definitions
open import SmallStepSemantics

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

uniqueness-of-normal-forms-and-end-states :
  ∀ {ty tyEnv s s1 s2} {t t₁ t₂ : Term ty} →
  Steps {ty} {tyEnv} s t s1 t₁ → Steps s t s2 t₂ → NF t₁ → NF t₂ → (t₁ , s1) == (t₂ , s2)
uniqueness-of-normal-forms-and-end-states Nil Nil nf1 nf2 = refl
uniqueness-of-normal-forms-and-end-states Nil (Cons x s3) nf1 nf2 = contradiction (nf1 (Reduces x))
uniqueness-of-normal-forms-and-end-states (Cons x s4) Nil nf1 nf2 = contradiction (nf2 (Reduces x))
uniqueness-of-normal-forms-and-end-states (Cons x s4) (Cons y s6) nf1 nf2 with deterministic-term x y , deterministic-TypeEnv x y
uniqueness-of-normal-forms-and-end-states (Cons x s5) (Cons y s6) nf1 nf2 | refl , refl with deterministic-state x y
uniqueness-of-normal-forms-and-end-states (Cons x s5) (Cons y s6) nf1 nf2 | refl , refl | refl = uniqueness-of-normal-forms-and-end-states s5 s6 nf1 nf2 -- 


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
