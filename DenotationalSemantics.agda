module DenotationalSemantics where

open import Lib
open import State
open import Definitions

data DValue : Type -> TypeEnv -> Set where
  vtrue : ∀{f} -> DValue BOOL f
  vfalse : ∀{f} -> DValue BOOL f
  vnat : ∀{f} ->  Nat -> DValue NAT f
  vvar : ∀{f} -> {ty : Type} -> (p : Pointer) -> f p == ty -> DValue (POINTER ty) f
  vnothing : ∀{f} -> DValue <> f


vcond : ∀{f} {a : Set} -> DValue BOOL f → a → a → a
vcond vtrue v2 v3 = v2
vcond vfalse v2 v3 = v3

vsucc : ∀{f} -> DValue NAT f -> DValue NAT f
vsucc (vnat x) = vnat (Succ x)

viszero : ∀{f} -> DValue NAT f -> DValue BOOL f
viszero (vnat Zero) = vtrue
viszero (vnat (Succ x)) = vfalse

-- State monad, based on Wouter Swierstra's thesis

-- Shape          <=>  TypeEnv
-- U              <=>  Type
-- u : Set        <=>  v : Value V
-- Ref            <=>  Pointer
-- Ref u s        <=>  p : Pointer , s p == u
-- el : U -> Set  <=>  Term
-- Cons u s       <=>   { {- TODO somewhere -} freePointer : Pointer } -> allocType u freePointer s

data St ( a : Type ) : TypeEnv → TypeEnv → Set where
  Return : forall { s } → DValue a s → St a s s
  Write : forall { s t u } → (p : Pointer) -> s p == u → DValue u s → St a s t → St a s t
  Read : forall { s t u } → (p : Pointer) -> s p == u -> ( DValue u s → St a s t ) → St a s t
  New : forall { s t u } → DValue u s → ({freePtr : Pointer} -> (p : Pointer) -> (allocType u freePtr s) p == u → St a ( allocType u freePtr s ) t ) → St a s t

return : forall { s a } → DValue a s → St a s s
return = Return

_>>=_ : ∀ { s t u a b } → St a s t → ( DValue a s → St b t u ) → St b s u
Return x >>= f = f x
Write p x x₁ v >>= f = Write p x x₁ (v >>= f)
Read p x x₁ >>= f = Read p x (\d -> x₁ d >>= f)
New d io >>= f = New d (\l freePtr -> io l freePtr >>= {!!})

bind = _>>=_

syntax bind m (\a -> b) = do a <- m then b

map : ∀ {a b f₁ f₂} -> (DValue a f₁ -> DValue b f₂) -> St a f₁ f₂ -> St b f₁ f₂
map f x = do x' <- x then
          return (f x')

vvar-pointer : ∀{ty f} -> DValue (POINTER ty) f -> Pointer
vvar-pointer (vvar x eq) = x

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
⟦ var x ⟧ = {!!}
⟦ ref x ⟧ =
  do x' <- ⟦ x ⟧ then
  New x' (λ p x₁ → {!return ?!})
⟦ x => x₁ ⟧ = 
  do x' <- ⟦ x ⟧ then
  do x₁' <- ⟦ x₁ ⟧ then
  return {!!}
⟦ x := x₁ ⟧ = 
  do x' <- ⟦ x ⟧ then
  do x₁' <- ⟦ x₁ ⟧ then -- FIXME: the small step semantics should be eager here!
  Write (vvar-pointer x') {!!} x₁' (return vnothing)
⟦ x % x₁ ⟧ = 
  do x' <- ⟦ x ⟧ then
  ⟦ x₁ ⟧
⟦ ! x ⟧ =
  do x' <- ⟦ x ⟧ then
  Read (vvar-pointer x') {!!} return
