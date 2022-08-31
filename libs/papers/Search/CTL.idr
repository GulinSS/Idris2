||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor
||| https://doi.org/10.1145/2976022.2976030

module Search.CTL

import Data.Nat
import Data.List.Lazy
import Data.List.Quantifiers
import Data.List.Lazy.Quantifiers

import public Search.Negation
import public Search.HDecidable
import public Search.Properties

%default total

------------------------------------------------------------------------
-- Type and some basic functions

||| Labeled transition diagram
public export
record Diagram (labels : Type) (state : Type) where
  constructor TD
  ||| Transition function
  transFn : (labels, state) -> List (labels, state)
  ||| Initial state
  iState : labels

%name Diagram td,td1,td2

||| Parallel composition of transition diagrams
public export
pComp :  {Lbls1, Lbls2, Sts : _}
      -> (td1 : Diagram Lbls1 Sts)
      -> (td2 : Diagram Lbls2 Sts)
      -> Diagram (Lbls1, Lbls2) Sts
pComp (TD transFn1 iState1) (TD transFn2 iState2) =
  TD compTransFn (iState1, iState2)
  where
    compTransFn : ((Lbls1, Lbls2), Sts) -> List ((Lbls1, Lbls2), Sts)
    compTransFn = (\ ((l1, l2), st) => 
                    map (\ (l1', st') => ((l1', l2), st')) (transFn1 (l1, st)) ++
                    map (\ (l2', st') => ((l1, l2'), st')) (transFn2 (l2, st)))

||| A computation tree (corecursive rose tree?)
data CT : Type where
  At : {Lbls, Sts : Type} -> (Lbls, Sts) -> Lazy (List CT) -> CT

||| Given a transition diagram and a starting value for the shared state,
||| construct the computation tree of the given transition diagram.
covering
model : {Lbls, Sts : _} -> Diagram Lbls Sts -> (st : Sts) -> CT
model (TD transFn iState) st = follow (iState, st)
  where
    follow : (Lbls, Sts) -> CT

    followAll : List (Lbls, Sts) -> List CT
    
    follow st = At st (followAll (transFn st))

    followAll [] = []
    followAll (st :: sts) = follow st :: followAll sts
    

-- different formulation of LTE, see also:
-- https://agda.github.io/agda-stdlib/Data.Nat.Base.html#4636
-- thanks @gallais!
public export
data LTE' : (n : Nat) -> (m : Nat) -> Type where
  LTERefl : LTE' m m
  LTEStep : LTE' n m -> LTE' n (S m)

||| Convert LTE' to LTE
lteAltToLTE : {m : _} -> LTE' n m -> LTE n m
lteAltToLTE {m=0} LTERefl = LTEZero
lteAltToLTE {m=(S k)} LTERefl = LTESucc (lteAltToLTE LTERefl)
lteAltToLTE {m=(S m)} (LTEStep s) = lteSuccRight (lteAltToLTE s)

lteAltIsLTE : LTE' n m === LTE n m

||| A formula has a bound (for Bounded Model Checking; BMC) and a computation
||| tree to check against.
public export
Formula : Type
Formula = (depth : Nat) -> (tree : CT) -> Type

||| A tree models a formula if there exists a depth d0 for which the property
||| holds for all depths d >= d0.
-- Called "satisfies" in the paper
public export
data Models : (m : CT) -> (f : Formula) -> Type where
  ItModels : (d0 : Nat) -> ({d : Nat} -> (d0 `LTE'` d) -> f d m) -> Models m f

------------------------------------------------------------------------
-- Depth invariance

||| Depth-invariance (DI) is when a formula cannot be falsified by increasing
||| the search depth.
public export
record DepthInv (f : Formula) where
  constructor DI
  prf : {n : Nat} -> {m : CT} -> f n m -> f (S n) m

||| A DI-formula holding for a specific depth means the CT models the formula in
||| general (we could increase the search depth and still be fine).
public export
diModels :  {n : Nat} -> {m : CT} -> {f : Formula} -> {auto d : DepthInv f}
         -> (p : f n m) -> Models m f
diModels {n} {f} {m} @{(DI diPrf)} p = ItModels n (\ q => diLTE p q)
  where
    diLTE : {n, n' : _} -> f n m -> (ltePrf' : n `LTE'` n') -> f n' m
    diLTE p LTERefl = p
    diLTE p (LTEStep x) = diPrf (diLTE p x)

||| A trivially true (TT) formula.
data TrueF : Formula where
  TT : {n : _} -> {m : _} -> TrueF n m

||| A tt formula is depth-invariant.
TrueDI : DepthInv TrueF
TrueDI = DI (const TT)

------------------------------------------------------------------------
-- Guards

namespace Guards
  ||| The formula `Guarded g` is true when the current state satisfies the guard
  ||| `g`.
  public export
  data Guarded : {Sts, Lbls : _} -> (g : (st : Sts) -> (l : Lbls) -> Type) -> Formula where
    Here :  {st : _} -> {l : _}
         -> {ms : Lazy (List CT)} -> {depth : Nat}
         -> {g : _}
         -> (guardOK : g st l)
         -> Guarded g depth (At (l, st) ms)

  ||| Guarded expressions are depth-inv as the guard does not care about depth.
  public export
  diGuarded : {p : _} -> DepthInv (Guarded p)
  diGuarded {p} = DI prf
    where
      prf : {n : _} -> {m : _} -> Guarded p n m -> Guarded p (S n) m
      prf (Here x) = Here x   -- can be interactively generated!

---  public export
---  data Guarded : {Sts, Lbls : _} -> (g : (st : Sts) -> (l : Lbls) -> Type) -> Formula where
---    Here :  {st : _} -> {l : _}
---         -> {ms : Lazy (List CT)} -> {depth : Nat}
---         -> g st l
---         -> Guarded g depth (At (l, st) ms)
---
---  public export
---  diGuarded : {p : _} -> DepthInv (Guarded (p st l))
---  diGuarded {p} = DI prf
---    where
---      prf : {n : _} -> {m : _} -> Guarded (p st l) n m -> Guarded (p st l) (S n) m
---      prf (Here x) = Here {depth=(S n)} x

------------------------------------------------------------------------
-- Conjunction / And

||| Conjunction of two `Formula`s
public export
data AND' : (f, g : Formula) -> Formula where
  MkAND' : {n : _} -> {m : _} -> f n m -> g n m -> (AND' f g) n m

||| Conjunction is depth-invariant
public export
diAND' :  {f, g : Formula}
       -> {auto p : DepthInv f}
       -> {auto q : DepthInv g}
       -> DepthInv (AND' f g)
diAND' @{(DI diP)} @{(DI diQ)} = DI (\ (MkAND' a b) => MkAND' (diP a) (diQ b))

------------------------------------------------------------------------
-- Always Until

namespace AU
  ---- -- FIXME: HOW??
  ---- data RTAll : {a : Type} -> (_ : (a -> Type)) -> List a -> Type where
  ----   Nil :  {p : (a -> Type)}
  ----       -> RTAll p []
  ----   (::) :  {x : a} -> {xs : List a} -> {p : (a -> Type)}
  ----        -> p x -> RTAll p xs -> RTAll p (x :: xs)

  ---- mapProperty : {a : _} -> {p : _} -> {q : _}
  ----             -> (p a -> q a) -> RTAll p l -> RTAll q l
  ---- mapProperty f [] = []
  ---- mapProperty f (p :: ps) = f p :: mapProperty f ps

  ||| A proof that for all paths in the tree, f holds until g does.
  public export
  data AlwaysUntil : (f, g : Formula) -> Formula where
    ||| We've found a place where g holds, so we're done.
    Here : {t : _} -> {n : _} -> g n t -> AlwaysUntil f g (S n) t
  
    ||| If f still holds and we can recursively show that g holds for all
    ||| possible subpaths in the CT, then all branches have f hold until g does.
    There :  {st : _} -> {lazyCTs : _} -> {n : _}
          -> f n (At st lazyCTs)
          ---- -> RTAll ((AlwaysUntil f g) n) lazyCTs
          -> All ((AlwaysUntil f g) n) lazyCTs
          -> AlwaysUntil f g (S n) (At st lazyCTs)

  ||| Provided `f` and `g` are depth-invariant, AlwaysUntil is depth-invariant
  public export
  diAU :  {f,g : _} -> {auto p : DepthInv f} -> {auto q : DepthInv g}
       -> DepthInv (AlwaysUntil f g)
  diAU @{(DI diP)} @{(DI diQ)} = DI prf
    where
      -- lemma : {d : _} -> RTAll (AlwaysUntil f g d) lt -> RTAll (AlwaysUntil f g (S d)) lt
      lemma :  {d : _} -> {lt : _}
            ---- -> RTAll (AlwaysUntil f g d) lt -> RTAll (AlwaysUntil f g (S d)) lt
            -> All (AlwaysUntil f g d) lt -> All (AlwaysUntil f g (S d)) lt

      prf : {d : _} -> {t : _} -> AlwaysUntil f g d t -> AlwaysUntil f g (S d) t

      lemma [] = []
      lemma (au :: aus) = (prf au) :: ?lemma_rhs_1 -- TODO: mapProperty prf xs

      prf (Here au) = Here (diQ au)
      prf (There au aus) = There (diP au) (lemma aus)

------------------------------------------------------------------------
-- Exists Until

namespace EU
  ||| A proof that somewhere in the tree, there is a path for which f holds
  ||| until g does.
  public export
  data ExistsUntil : (f, g : Formula) -> Formula where
    ||| If g holds here, we've found a branch where we can stop.
    Here : {t : _} -> {n : _} -> g n t -> ExistsUntil f g (S n) t

    ||| If f holds here and any of the further branches have a g, then there is
    ||| a branch where f holds until g does.
    There :  {st : _} -> {ms : _} -> {n : _}
          -> f n (At st ms)
          -> Any (ExistsUntil f g n) ms
          -> ExistsUntil f g (S n) (At st ms)

  ||| Provided `f` and `g` are depth-invariant, ExistsUntil is depth-invariant.
  public export
  diEU :  {f, g : _} -> {auto p : DepthInv f} -> {auto q : DepthInv g}
       -> DepthInv (ExistsUntil f g)
  diEU @{(DI diP)} @{(DI diQ)} = DI prf
    where
      prf :  {d : _} -> {t : _}
          -> ExistsUntil f g d t
          -> ExistsUntil f g (S d) t
      prf (Here eu) = Here (diQ eu)
      prf (There eu eus) = There (diP eu) ?prf_rhs_1  -- TODO: same err as AU

------------------------------------------------------------------------
-- Completed, and the stronger forms of Global

||| A completed formula is a formula for which no more successor states exist.
public export
data Completed : Formula where
  IsComplete :  {st : _} -> {n : _} -> {ms : _}
             -> ms === []
             -> Completed n (At st ms)

||| A completed formula is depth-invariant (there is nothing more to do).
public export
diCompleted : DepthInv Completed
diCompleted = DI prf
  where
    prf : {d : _} -> {t : _} -> Completed d t -> Completed (S d) t
    prf (IsComplete p) = IsComplete p

||| We can only handle always global checks on finite paths.
public export
alwaysGlobal : (f : Formula) -> Formula
alwaysGlobal f = (AlwaysUntil f f) `AND'` Completed

||| We can only handle exists global checks on finite paths.
public export
existsGlobal : (f : Formula) -> Formula
existsGlobal f = (ExistsUntil f f) `AND'` Completed

------------------------------------------------------------------------
-- Proof search (finally!)

||| Model-checking is a half-decider for the formula `f`
MC : (f : Formula) -> Type
MC f = (t : CT) -> (d : Nat) -> HDec (f d t)

||| Proof-search combinator for guards.
now :  {Sts, Lbls : _}
    -> {g : (st : Sts) -> (l : Lbls) -> Type}
    -> {hdec : _}
    -> {auto p : AnHDec hdec}
    -> ((st : Sts) -> (l : Lbls) -> hdec (g st l))
    -> MC (Guarded g)
-- FIXME: mismatch between the `Sts` and `Lbls` here, and the ones in the type
-- of `Guarded`. This is a problem which needs to be solved...
-- now f (At (l', st') ms) _ = [| Here (toHDec (f st' l')) |]
