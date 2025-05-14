module Core.Termination.CallGraph

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Options
import Core.Value
import Core.Name.CompatibleVars

import Libraries.Data.List.SizeOf

import Libraries.Data.IntMap
import Libraries.Data.SparseMatrix
import Libraries.Data.SnocList.SizeOf

import Data.String

%default covering

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

sizeEq : {auto 0 cv : CompatibleVars rhsVars lhsVars} ->
         Term rhsVars -> -- RHS
         Term lhsVars -> -- LHS: may contain dot-patterns, try both sides of as patterns
         Bool
sizeEq (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
sizeEq (Ref _ _ n) (Ref _ _ n') = n == n'
sizeEq (Meta _ _ i args) (Meta _ _ i' args')
    -- = i == i' && assert_total (all (uncurry sizeEq) (zip args args'))
    = i == i' && assert_total (all (uncurry sizeEq) (zip (map snd args) (map snd args')))
sizeEq (Bind _ _ b sc) (Bind _ _ b' sc') = eqBinderBy sizeEq b b' && sizeEq sc sc'
sizeEq (App _ f _ a) (App _ f' _ a') = sizeEq f f' && sizeEq a a'
sizeEq (As _ _ a p) p' = sizeEq p p'
sizeEq p (As _ _ a p') = sizeEq p a || sizeEq p p'
sizeEq (TDelayed _ _ t) (TDelayed _ _ t') = sizeEq t t'
sizeEq (TDelay _ _ t x) (TDelay _ _ t' x') = sizeEq t t' && sizeEq x x'
sizeEq (TForce _ _ t) (TForce _ _ t') = sizeEq t t'
sizeEq (PrimVal _ c) (PrimVal _ c') = c == c'
-- traverse dotted LHS terms
sizeEq t (Erased _ (Dotted t')) = eqTerm t t' -- t' is no longer a pattern
sizeEq (TType _ _) (TType _ _) = True
sizeEq _ _ = False

-- Remove all force and delay annotations which are nothing to do with
-- coinduction meaning that all Delays left guard coinductive calls.
delazy : Defs -> Term vars -> Term vars
delazy defs (TDelayed fc r tm)
    = let tm' = delazy defs tm in
          case r of
               LInf => TDelayed fc r tm'
               _ => tm'
delazy defs (TDelay fc r ty tm)
    = let ty' = delazy defs ty
          tm' = delazy defs tm in
          case r of
               LInf => TDelay fc r ty' tm'
               _ => tm'
delazy defs (TForce fc r t)
    = case r of
           LInf => TForce fc r (delazy defs t)
           _ => delazy defs t
delazy defs (Meta fc n i args) = Meta fc n i (map @{Compose} (delazy defs) args)
delazy defs (Bind fc x b sc)
    = Bind fc x (map (delazy defs) b) (delazy defs sc)
delazy defs (App fc f c a) = App fc (delazy defs f) c (delazy defs a)
delazy defs (As fc s a p) = As fc s (delazy defs a) (delazy defs p)
delazy defs tm = tm

-- Expand the size change argument list with 'Nothing' to match the given
-- arity (i.e. the arity of the function we're calling) to ensure that
-- it's noted that we don't know the size change relationship with the
-- extra arguments.
expandToArity : Nat -> List (Maybe (Nat, SizeChange)) ->
                List (Maybe (Nat, SizeChange))
expandToArity Z xs = xs
expandToArity (S k) (x :: xs) = x :: expandToArity k xs
expandToArity (S k) [] = Nothing :: expandToArity k []

mutual
  findSC : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Defs -> Env Term vars -> Guardedness ->
           List (Term vars) -> -- LHS args
           Term vars -> -- RHS
           Core (List SCCall)
  findSC {vars} defs env g pats (Bind fc n b sc)
       = pure $
            !(findSCbinder b) ++
            !(findSC defs (env :< b) g (map weaken pats) sc)
    where
      findSCbinder : Binder (Term vars) -> Core (List SCCall)
      findSCbinder (Let _ c val ty) = findSC defs env g pats val
      findSCbinder b = pure [] -- only types, no need to look
  -- If we're Guarded and find a Delay, continue with the argument as InDelay
  findSC defs env Guarded pats (TDelay _ _ _ tm)
      = findSC defs env InDelay pats tm
  findSC defs env g pats (TDelay _ _ _ tm)
      = findSC defs env g pats tm
  findSC defs env g pats tm
      = do let (fn, args) = getFnArgs tm
           -- if it's a 'case' or 'if' just go straight into the arguments
           Nothing <- handleCase fn args
               | Just res => pure res
           fn' <- conIfGuarded fn -- pretend it's a data constructor if
                                  -- it has the AllGuarded flag
           case (g, fn', args) of
    -- If we're InDelay and find a constructor (or a function call which is
    -- guaranteed to return a constructor; AllGuarded set), continue as InDelay
             (InDelay, Ref fc (DataCon _ _) cn, args) =>
                 do scs <- traverse (findSC defs env InDelay pats) args
                    pure (concat scs)
             -- If we're InDelay otherwise, just check the arguments, the
             -- function call is okay
             (InDelay, _, args) =>
                 do scs <- traverse (findSC defs env Unguarded pats) args
                    pure (concat scs)
             (Guarded, Ref fc (DataCon _ _) cn, args) =>
                    findSCcall defs env Guarded pats fc cn args
             (Toplevel, Ref fc (DataCon _ _) cn, args) =>
                    findSCcall defs env Guarded pats fc cn args
             (_, Ref fc Func fn, args) =>
                 do logC "totality" 50 $
                       pure $ "Looking up type of " ++ show !(toFullNames fn)
                    findSCcall defs env Unguarded pats fc fn args
             (_, f, args) =>
                 do scs <- traverse (findSC defs env Unguarded pats) args
                    pure (concat scs)
      where
        handleCase : Term vars -> List (Term vars) -> Core (Maybe (List SCCall))
        handleCase (Ref fc nt n) args
            = do n' <- toFullNames n
                 if caseFn n'
                    then Just <$> findSCcall defs env g pats fc n args
                    else pure Nothing
        handleCase _ _ = pure Nothing

        conIfGuarded : Term vars -> Core (Term vars)
        conIfGuarded (Ref fc Func n)
            = do defs <- get Ctxt
                 Just gdef <- lookupCtxtExact n (gamma defs)
                      | Nothing => pure $ Ref fc Func n
                 if AllGuarded `elem` flags gdef
                    then pure $ Ref fc (DataCon 0 0) n
                    else pure $ Ref fc Func n
        conIfGuarded tm = pure tm

  knownOr : Core SizeChange -> Core SizeChange -> Core SizeChange
  knownOr x y = case !x of Unknown => y; _ => x

  plusLazy : Core SizeChange -> Core SizeChange -> Core SizeChange
  plusLazy x y = case !x of Smaller => pure Smaller; x => pure $ x |+| !y

  -- Return whether first argument is structurally smaller than the second.
  sizeCompare : {auto defs : Defs} ->
                Nat -> -- backtracking fuel
                Term vars -> -- RHS: term we're checking
                Term vars -> -- LHS: argument it might be smaller than
                Core SizeChange

  sizeCompareCon : {auto defs : Defs} -> Nat -> Term vars -> Term vars -> Core Bool
  sizeCompareTyCon : {auto defs : Defs} -> Nat -> Term vars -> Term vars -> Core Bool
  sizeCompareConArgs : {auto defs : Defs} -> Nat -> Term vars -> List (Term vars) -> Core Bool
  sizeCompareApp : {auto defs : Defs} -> Nat -> Term vars -> Term vars -> Core SizeChange

  sizeCompare fuel s (Erased _ (Dotted t)) = sizeCompare fuel s t
  sizeCompare fuel _ (Erased _ _) = pure Unknown -- incomparable!
  -- for an as pattern, it's smaller if it's smaller than either part
  sizeCompare fuel s (As _ _ p t)
      = knownOr (sizeCompare fuel s p) (sizeCompare fuel s t)
  sizeCompare fuel (As _ _ p s) t
      = knownOr (sizeCompare fuel p t) (sizeCompare fuel s t)
  -- if they're both metas, let sizeEq check if they're the same
  sizeCompare fuel s@(Meta _ _ _ _) t@(Meta _ _ _ _) = pure (if sizeEq s t then Same else Unknown)
  -- otherwise try to expand RHS meta
  sizeCompare fuel s@(Meta n _ i args) t = do
    Just gdef <- lookupCtxtExact (Resolved i) (gamma defs) | _ => pure Unknown
    let (Function _ tm _ _) = definition gdef | _ => pure Unknown
    tm <- substMeta (embed tm) (map snd args) zero ScopeEmpty
    sizeCompare fuel tm t
    where
      substMeta : {0 drop, vs : _} ->
                  Term (vs ++ drop) -> List (Term vs) ->
                  SizeOf drop -> SubstEnv drop vs ->
                  Core (Term vs)
      substMeta (Bind bfc n (Lam _ c e ty) sc) (a :: as) drop env
          = substMeta sc as (suc drop) (env :< a)
      substMeta (Bind bfc n (Let _ c val ty) sc) as drop env
          = substMeta (subst val sc) as drop env
      substMeta rhs [] drop env = pure (substs drop env rhs)
      substMeta rhs _ _ _ = throw (InternalError ("Badly formed metavar solution \{show n}"))

  sizeCompare fuel s t
     = if !(sizeCompareTyCon fuel s t) then pure Same
       else if !(sizeCompareCon fuel s t)
          then pure Smaller
          else knownOr (sizeCompareApp fuel s t) (pure $ if sizeEq s t then Same else Unknown)

  sizeCompareProdConArgs : {auto defs : Defs} -> Nat -> List (Term vars) -> List (Term vars) -> Core SizeChange
  sizeCompareProdConArgs _ [] [] = pure Same
  sizeCompareProdConArgs fuel (x :: xs) (y :: ys) =
    case !(sizeCompare fuel x y) of
      Unknown => pure Unknown
      t => (t |*|) <$> sizeCompareProdConArgs fuel xs ys
  sizeCompareProdConArgs _ _ _ = pure Unknown

  sizeCompareTyCon fuel s t =
    let (f, args) = getFnArgs t in
    let (g, args') = getFnArgs s in
    case f of
      Ref _ (TyCon _) cn => case g of
        Ref _ (TyCon _) cn' => if cn == cn'
            then (Unknown /=) <$> sizeCompareProdConArgs fuel args' args
            else pure False
        _ => pure False
      _ => pure False

  sizeCompareCon fuel s t
      = let (f, args) = getFnArgs t in
        case f of
             Ref _ (DataCon t a) cn =>
                -- if s is smaller or equal to an arg, then it is smaller than t
                if !(sizeCompareConArgs (minus fuel 1) s args) then pure True
                else let (g, args') = getFnArgs s in
                    case (fuel, g) of
                        (S k, Ref _ (DataCon t' a') cn') => do
                                -- if s is a matching DataCon, applied to same number of args,
                                -- no Unknown args, and at least one Smaller
                                if cn == cn' && length args == length args'
                                  then (Smaller ==) <$> sizeCompareProdConArgs k args' args
                                  else pure False
                        _ => pure $ False
             _ => pure False

  sizeCompareConArgs _ s [] = pure False
  sizeCompareConArgs fuel s (t :: ts)
      = case !(sizeCompare fuel s t) of
          Unknown => sizeCompareConArgs fuel s ts
          _ => pure True

  sizeCompareApp fuel (App _ f _ _) t = sizeCompare fuel f t
  sizeCompareApp _ _ t = pure Unknown

  sizeCompareAsserted : {auto defs : Defs} -> Nat -> Maybe (Term vars) -> Term vars -> Core SizeChange
  sizeCompareAsserted fuel (Just s) t
      = pure $ case !(sizeCompare fuel s t) of
          Unknown => Unknown
          _ => Smaller
  sizeCompareAsserted _ Nothing _ = pure Unknown

  -- if the argument is an 'assert_smaller', return the thing it's smaller than
  asserted : Name -> Term vars -> Maybe (Term vars)
  asserted aSmaller tm
       = case getFnArgs tm of
              (Ref _ nt fn, [_, _, b, _])
                   => if fn == aSmaller
                         then Just b
                         else Nothing
              _ => Nothing

  -- Calculate the size change for the given argument.  i.e., return the
  -- relative size of the given argument to each entry in 'pats'.
  mkChange : Defs -> Name ->
             (pats : List (Term vars)) ->
             (arg : Term vars) ->
             Core (List SizeChange)
  mkChange defs aSmaller pats arg
    = let fuel = defs.options.elabDirectives.totalLimit
      in traverse (\p => plusLazy (sizeCompareAsserted fuel (asserted aSmaller arg) p) (sizeCompare fuel arg p)) pats

  findSCcall : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Defs -> Env Term vars -> Guardedness ->
               List (Term vars) ->
               FC -> Name -> List (Term vars) ->
               Core (List SCCall)
  findSCcall defs env g pats fc fn_in args
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = do fn <- getFullName fn_in
           logC "totality.termination.sizechange" 10 $ do pure $ "Looking under " ++ show !(toFullNames fn)
           aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
           logC "totality.termination.sizechange" 10 $
               do under <- traverse toFullNames pats
                  targs <- traverse toFullNames args
                  pure ("Under " ++ show under ++ "\n" ++ "Args " ++ show targs)
           if fn == NS builtinNS (UN $ Basic "assert_total")
              then pure []
              else
               do scs <- traverse (findSC defs env g pats) args
                  pure ([MkSCCall fn
                           (fromListList
                                !(traverse (mkChange defs aSmaller pats) args))
                           fc]
                           ++ concat scs)

  findInCase : {auto c : Ref Ctxt Defs} ->
               Defs -> Guardedness ->
               (vs ** (Env Term vs, List (Term vs), Term vs)) ->
               Core (List SCCall)
  findInCase defs g (_ ** (env, pats, tm))
     = do logC "totality" 10 $
                   do ps <- traverse toFullNames pats
                      pure ("Looking in case args " ++ show ps)
          logTermNF "totality" 10 "        =" env tm
          rhs <- normaliseOpts tcOnly defs env tm
          findSC defs env g pats (delazy defs rhs)

findCalls : {auto c : Ref Ctxt Defs} ->
            Defs -> Clause ->
            Core (List SCCall)
findCalls defs (MkClause env lhs rhs_in)
   = do let pargs = getArgs (delazy defs lhs)
        rhs <- normaliseOpts tcOnly defs env rhs_in
        findSC defs env Toplevel pargs (delazy defs rhs)

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ _ _ (Just pats))
   = do sc <- traverse (findCalls defs) pats
        pure $ nub (concat sc)
getSC defs (Function _ _ _ Nothing) = pure []
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do logC "totality.termination.sizechange" 5 $ do pure $ "Calculating Size Change: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         getSC defs (definition def)
