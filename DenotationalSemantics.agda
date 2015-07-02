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

-- Associate each value with a term.
⌜'_⌝ : forall {ty f} -> DValue ty f → Term ty
⌜' vtrue ⌝ = true
⌜' vfalse ⌝ = false
⌜' vnat k ⌝ = natTerm k
⌜' vvar n e ⌝ = var n
⌜' vnothing ⌝ = <>

vcond : ∀{f} {a : Set} -> DValue BOOL f → a → a → a
vcond vtrue v2 v3 = v2
vcond vfalse v2 v3 = v3

vcond'' : ∀{f} {a : Set₁} -> DValue BOOL f → a → a → a
vcond'' vtrue v2 v3 = v2
vcond'' vfalse v2 v3 = v3

vcond' : ∀{f} {a b : Set} -> (c : DValue BOOL f) → a → b → (vcond'' c a b)
vcond' vtrue v2 v3 = v2
vcond' vfalse v2 v3 = v3

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

_>>=_ : ∀ { s t u a b } → St a s t → ( DValue a t → St b t u ) → St b s u
Return x >>= f = f x
Write p x x₁ v >>= f = Write p x x₁ (v >>= f)
Read p x x₁ >>= f = Read p x (\d -> x₁ d >>= f)
New d io >>= f = New d (\l freePtr -> io l freePtr >>= f)

bind = _>>=_

syntax bind m (\a -> b) = do a <- m then b

map : ∀ {a b f₁ f₂} -> (DValue a f₂ -> DValue b f₂) -> St a f₁ f₂ -> St b f₁ f₂
map f x = do x' <- x then
          return (f x')

vvar-pointer : ∀{ty f} -> DValue (POINTER ty) f -> Pointer
vvar-pointer (vvar x eq) = x

extend : ∀{ty} -> Term ty -> TypeEnv -> TypeEnv
⟦_⟧ : ∀ {ty f} -> (t : Term ty) -> St ty f (extend t f)
run : ∀ {ty f f'} -> St ty f f' -> State f -> Tuple (DValue ty f') (State f')

run ( Return x ) h = ( x , h )
run ( Write loc d e io ) h = run io (store loc ⌜' e ⌝ d h)
run ( Read loc e io ) h = run ( io {!get h loc !}) h {- io (h ! loc) -}
run ( New d io ) h = run ( {!!} ) ( {!!} d h )
-- New : forall { s t u } → el u → ( Ref u ( Cons u s ) → IO a ( Cons u s ) t ) → IO a s t
-- ... >>= ...
-- New d io >>= f = New d ( λl → io l >> = f )
-- ... run ...
-- run ( New d io ) h = run ( io Top ) ( Alloc d h )

extend true f = f
extend false f = f
extend <> f = f
extend zero f = f
extend (var x) f = f
extend (if t then t₁ else t₂) f x with run (⟦_⟧ {f = f} t) {!!}
extend (if t then t₁ else t₂) f x | vtrue , _ = extend t₁ (extend t f) x
extend (if t then t₁ else t₂) f x | vfalse , _ = extend t₂ (extend t f) x
extend (succ t) f = extend t f
extend (iszero t) f = extend t f
extend (ref t) f = extend t f -- TODO alloc
extend (t => t₁) f = extend t₁ (extend t f)
extend (t := t₁) f = extend t₁ (extend t f)
extend (t % t₁) f = extend t₁ (extend t f)
extend (! t) f = extend t f

⟦ true ⟧ = return vtrue
⟦ false ⟧ = return vfalse
⟦ zero ⟧ = return (vnat Zero)
⟦ <> ⟧ = return vnothing
⟦ succ x ⟧ = do x' <- ⟦ x ⟧ then
             return x'
⟦_⟧ (if x then x₁ else x₂) with run ⟦ x ⟧ {!!}
... | xx = {!⟦ x ⟧ >>= (\{
    vtrue -> ⟦ x₁ ⟧ ;
    vfalse -> ⟦ x₂ ⟧
  })!}
⟦_⟧ {f = f} (iszero x) = 
  do x' <- ⟦ x ⟧ then
  return (viszero x')
⟦ var x ⟧ = return (vvar x {!!})
⟦ ref x ⟧ =
  do x' <- ⟦ x ⟧ then
  New x' (λ p x₁ → {!return (vvar ? ?)!})
⟦ x => x₁ ⟧ =
  do x' <- ⟦ x ⟧ then
  do x₁' <- ⟦ x₁ ⟧ then
  {!TODO reassign pointer!}
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
