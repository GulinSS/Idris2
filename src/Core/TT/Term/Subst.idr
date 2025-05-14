module Core.TT.Term.Subst

import Algebra
import Core.Name
import Core.Name.Scoped

import Core.TT.Binder
import Core.TT.Subst
import Core.TT.Term
import Core.TT.Var

import Data.List
import Data.SnocList

import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf

%default total

public export
SubstEnv : Scope -> Scoped
SubstEnv = Subst Term

ScopeSingle : Term vars -> SubstEnv [<x] vars
ScopeSingle n = [<n]

substTerm : Substitutable Term Term
substTerms : Substitutable Term (List . Term)
substBinder : Substitutable Term (Binder . Term)
substTaggedTerms : forall a. Substitutable Term (List . (a,) . Term)
substAlt : Substitutable Term CaseAlt
substCaseScope : Substitutable Term CaseScope

substTerm outer dropped env (Local fc r _ prf)
    = find (\ (MkVar p) => Local fc r _ p) outer dropped (MkVar prf) env
substTerm outer dropped env (Ref fc x name) = Ref fc x name
substTerm outer dropped env (Meta fc n i xs)
    = Meta fc n i (substTaggedTerms outer dropped env xs)
substTerm outer dropped env (Bind fc x b scope)
    = Bind fc x (substBinder outer dropped env b)
                (substTerm (suc outer) dropped env scope)
substTerm outer dropped env (App fc fn c arg)
    = App fc (substTerm outer dropped env fn) c (substTerm outer dropped env arg)
substTerm outer dropped env (As fc s as pat)
    = As fc s (substTerm outer dropped env as) (substTerm outer dropped env pat)
substTerm outer dropped env (Case fc t c sc scty alts)
    = Case fc t c (substTerm outer dropped env sc)
                  (substTerm outer dropped env scty)
                  (map (assert_total $ substAlt outer dropped env) alts)
substTerm outer dropped env (TDelayed fc x y) = TDelayed fc x (substTerm outer dropped env y)
substTerm outer dropped env (TDelay fc x t y)
    = TDelay fc x (substTerm outer dropped env t) (substTerm outer dropped env y)
substTerm outer dropped env (TForce fc r x) = TForce fc r (substTerm outer dropped env x)
substTerm outer dropped env (PrimVal fc c) = PrimVal fc c
substTerm outer dropped env (Erased fc Impossible) = Erased fc Impossible
substTerm outer dropped env (Erased fc Placeholder) = Erased fc Placeholder
substTerm outer dropped env (Erased fc (Dotted t)) = Erased fc (Dotted (substTerm outer dropped env t))
substTerm outer dropped env (Unmatched fc u) = Unmatched fc u
substTerm outer dropped env (TType fc u) = TType fc u

substTerms outer dropped env xs
  = assert_total $ map (substTerm outer dropped env) xs

substBinder outer dropped env b
  = assert_total $ map (substTerm outer dropped env) b

substTaggedTerms outer dropped env b
  = assert_total $ map @{Compose} (substTerm outer dropped env) b

substCaseScope outer dropped env (RHS tm) = RHS (substTerm outer dropped env tm)
substCaseScope outer dropped env (Arg c x sc) = Arg c x (substCaseScope (suc outer) dropped env sc)

substAlt outer dropped env (ConCase n t sc) = ConCase n t (substCaseScope outer dropped env sc)
substAlt outer dropped env (DelayCase ty arg sc) = DelayCase ty arg (substTerm (suc (suc outer)) dropped env sc)
substAlt outer dropped env (ConstCase c sc) = ConstCase c (substTerm outer dropped env sc)
substAlt outer dropped env (DefaultCase sc) = DefaultCase (substTerm outer dropped env sc)

export
substs : SizeOf dropped -> SubstEnv dropped vars -> Term (vars ++ dropped) -> Term vars
substs dropped env tm = substTerm zero dropped env tm

export
subst : Term vars -> Term (vars :< x) -> Term vars
subst val tm = substs (suc zero) (ScopeSingle val) tm
