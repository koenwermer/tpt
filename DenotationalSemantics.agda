module DenotationalSemantics where

open import Lib
open import State
open import Definitions

vcond : {a : Set} -> Value BOOL → a → a → a
vcond vtrue v2 v3 = v2
vcond vfalse v2 v3 = v3

vsucc : Value NAT -> Value NAT
vsucc (vnat x) = vnat (Succ x)

viszero : Value NAT -> Value BOOL
viszero (vnat Zero) = vtrue
viszero (vnat (Succ x)) = vfalse

-- State monad, based on Wouter Swierstra's thesis

-- Shape <=> TypeEnv
-- U       <=>   Type
-- u : Set   <=>   v : Value V
-- Ref       <=>   Pointer
-- Ref u s   <=>   p : Pointer , s p == u
-- el : U -> Set   <=>   Term
-- Cons u s     <=>    { {- TODO somewhere -} freePointer : Pointer } -> allocType u freePointer s

data St ( a : Type ) : TypeEnv → TypeEnv → Set where
  Return : forall { s } → Value a → St a s s
  Write : forall { s t u } → (p : Pointer) -> s p == u → Value u → St a s t → St a s t
  Read : forall { s t u } → (p : Pointer) -> s p == u -> ( Value u → St a s t ) → St a s t
  New : forall { s t u } → {freePtr : Pointer} -> Value u → ( (p : Pointer) -> (allocType u freePtr s) p == u → St a ( allocType u freePtr s ) t ) → St a s t

return : forall { s a } → Value a → St a s s
return = Return

_>>=_ : ∀ { s t u a b } → St a s t → ( Value a → St b t u ) → St b s u
Return x >>= f = f x
Write p x x₁ v >>= f = Write p x x₁ (v >>= f)
Read p x x₁ >>= f = Read p x (\d -> x₁ d >>= f)
New d io >>= f = New d (\l freePtr -> io l freePtr >>= f)

bind = _>>=_

syntax bind m (\a -> b) = do a <- m then b

map : ∀ {a b f₁ f₂} -> (Value a -> Value b) -> St a f₁ f₂ -> St b f₁ f₂
map f x = do x' <- x then
          return (f x')

⟦_⟧ : ∀ {ty f} -> Term ty -> St ty f f
⟦ true ⟧ = return vtrue
⟦ false ⟧ = return vfalse
⟦ zero ⟧ = return (vnat Zero)
⟦ <> ⟧ = return vnothing
⟦ succ x ⟧ = map vsucc ⟦ x ⟧
⟦ if x then x₁ else x₂ ⟧ = 
   do x' <- ⟦ x ⟧ then
   vcond x' ⟦ x₁ ⟧ ⟦ x₂ ⟧
⟦ iszero x ⟧ = map viszero ⟦ x ⟧
⟦ var x ⟧ = return (vvar x)
⟦ ref x ⟧ = map {!!} ⟦ x ⟧
⟦ x => x₁ ⟧ = 
  do x' <- ⟦ x ⟧ then
  do x₁' <- ⟦ x₁ ⟧ then
  return {!!}
⟦ x := x₁ ⟧ = 
  do x' <- ⟦ x ⟧ then
  do x₁' <- ⟦ x₁ ⟧ then -- FIXME: the small step semantics is eager here!
  return {!!}
⟦ x % x₁ ⟧ = 
  do x' <- ⟦ x ⟧ then
  do x₁' <- ⟦ x₁ ⟧ then
  return {!!}
⟦ ! x ⟧ = map {!!} ⟦ x ⟧
