module SmallStepSemantics where

open import State
open import Definitions
open import Lib
open import SmallStepSemantics.Step public
open import SmallStepSemantics.Deterministic using
 ( deterministic-term
 ; deterministic-TypeEnv
 ; deterministic-state ) public

-- Types are preserved during evaluation
preservation : forall {ty : Type} {f : TypeEnv} {s s' : State f} -> (t t' : Term ty) -> Step s t s' t' -> ty == ty
preservation t t' step = refl

uniqueness-of-normal-forms-and-end-states :
  ∀ {ty tyEnv s s1 s2} {t t₁ t₂ : Term ty} →
  Steps {ty} {tyEnv} s t s1 t₁ → Steps s t s2 t₂ → NF t₁ → NF t₂ → (t₁ , s1) == (t₂ , s2)
uniqueness-of-normal-forms-and-end-states Nil Nil nf1 nf2 = refl
uniqueness-of-normal-forms-and-end-states Nil (Cons x s3) nf1 nf2 = contradiction (nf1 (Reduces x))
uniqueness-of-normal-forms-and-end-states (Cons x s4) Nil nf1 nf2 = contradiction (nf2 (Reduces x))
uniqueness-of-normal-forms-and-end-states (Cons x s4) (Cons y s6) nf1 nf2 with deterministic-term x y , deterministic-TypeEnv x y
uniqueness-of-normal-forms-and-end-states (Cons x s5) (Cons y s6) nf1 nf2 | refl , refl with deterministic-state x y
uniqueness-of-normal-forms-and-end-states (Cons x s5) (Cons y s6) nf1 nf2 | refl , refl | refl = uniqueness-of-normal-forms-and-end-states s5 s6 nf1 nf2 -- 
