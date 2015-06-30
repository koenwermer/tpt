module State where

open import Lib
open import Definitions

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

allocType-preserve : ∀ ty maxPointer tyEnv x -> Not (x == maxPointer) -> (allocType ty maxPointer tyEnv) x == tyEnv x
allocType-preserve ty maxPointer tyEnv x _ with x `eq` maxPointer
allocType-preserve ty maxPointer tyEnv _ not | Left r = contradiction (not r)
allocType-preserve ty maxPointer tyEnv x _ | Right x₁ = refl

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

alloc-pointer : {ty : Type} {typeOf : TypeEnv} -> (t : Term ty) -> (s : State typeOf) -> fst (alloc {ty} {typeOf} t s) == var (getPointerLimit s)
alloc-pointer t (state f pointerLimit x) = refl

-- Gets an expression from a cell
get : {typeOf : TypeEnv} -> State typeOf -> (n : Pointer) -> Term (typeOf n)
get s n = getEq s n refl

