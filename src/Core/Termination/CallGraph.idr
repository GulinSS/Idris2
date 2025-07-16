module Core.Termination.CallGraph

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Options
import Core.Evaluate.Value
import Core.Evaluate.Normalise
import Core.Evaluate
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

sizeEq : Value f vars -> -- RHS
       Value f' vars -> -- LHS: may contain dot-patterns, try both sides of as patterns
       Core Bool

-- Substitute a name with what we know about it.
-- We assume that the name has come from a case pattern, which means we're
-- not going to have to look under binders.
-- We also assume that (despite the 'Glued') it's always a VDCon or VDelay
-- therefore no need to expand apps.
substNameInVal : Name -> Glued vars -> Glued vars -> Core (Glued vars)
-- Only interested in Bound names (that we just made) and so we only need
-- to check the index
substNameInVal (MN _ i') rep tm@(VApp _ Bound (MN _ i) _ _)
    = if i == i' then pure rep else pure tm
substNameInVal n rep (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(substNameInSpine sp)
  where
    substNameInSpine : Spine vars -> Core (Spine vars)
    substNameInSpine [<] = pure [<]
    substNameInSpine (rest :< MkSpineEntry fc c arg)
        = do rest' <- substNameInSpine rest
             pure (rest' :< MkSpineEntry fc c (substNameInVal n rep !arg))
substNameInVal n rep (VDelay fc r t v)
    = pure $ VDelay fc r !(substNameInVal n rep t) !(substNameInVal n rep v)
substNameInVal n rep tm = pure tm

replaceInArgs : {auto c : Ref Ctxt Defs} -> Name -> Glued [<] ->
                List (Glued [<]) -> Core (List (Glued [<]))
replaceInArgs v tm [] = pure []
-- -- Don't copy if there's no substitution done!
replaceInArgs v tm (arg :: args)
    = do arg' <- substNameInVal v tm arg
         logC "totality.termination.sizechange" 10 $
             do v' <- toFullNames v
                tm' <- toFullNames !(quote [<] tm)
                arg'' <- toFullNames !(quote [<] arg)
                arg''' <- toFullNames !(quote [<] arg')
                pure ("replaceInArgs v: \{show v'}, tm: \{show tm'}, arg: \{show arg''} |=> arg': \{show arg'''}")

         if !(sizeEq arg arg')
            then pure $ arg :: !(replaceInArgs v tm args)
            else pure $ arg' :: !(replaceInArgs v tm args)

expandForced : {auto c : Ref Ctxt Defs} -> List (Glued [<], Glued [<]) ->
               List (Glued [<]) -> Core (List (Glued [<]))
expandForced [] args = pure args
-- Only useful if the equality evaluated to a bound name that we know about
expandForced ((VApp _ Bound n _ _, tm) :: fs) args
    = expandForced fs !(replaceInArgs n tm args)
expandForced (_ :: fs) args = expandForced fs args

data SCVar : Type where

mkvar : Int -> Value f [<]
mkvar i = VApp EmptyFC Bound (MN "scv" i) [<] (pure Nothing)

nextVar : {auto c : Ref SCVar Int} -> Core (Value f [<])
nextVar
    = do v <- get SCVar
         put SCVar (v + 1)
         pure (mkvar v)

ForcedEqs : Type
ForcedEqs = List (Glued [<], Glued [<])

findVar : Int -> List (Glued vars, Glued vars) -> Maybe (Glued vars)
findVar i [] = Nothing
findVar i ((VApp _ Bound (MN _ i') _ _, tm) :: eqs)
    = if i == i' then Just tm else findVar i eqs
findVar i (_ :: eqs) = findVar i eqs

canonicalise : List (Glued vars, Glued vars) -> Glued vars -> Core (Glued vars)
canonicalise eqs tm@(VApp _ Bound (MN _ i) _ _)
    = case findVar i eqs of
           Nothing => pure tm
           Just val => canonicalise eqs val
canonicalise eqs (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(canonSp sp)
  where
    canonSp : Spine vars -> Core (Spine vars)
    canonSp [<] = pure [<]
    canonSp (rest :< MkSpineEntry fc c arg)
        = do rest' <- canonSp rest
             pure (rest' :< MkSpineEntry fc c (canonicalise eqs !arg))
-- for matching on types, convert to the form the case tree builder uses
canonicalise eqs (VPrimVal fc (PrT c))
    = pure $ (VTCon fc (UN (Basic $ show c)) 0 [<])
canonicalise eqs (VType fc _)
    = pure $ (VTCon fc (UN (Basic "Type")) 0 [<])
canonicalise eqs val = pure val

scEqSpine : Spine vars -> Spine vars -> Core Bool
scEqSpine [<] [<] = pure True
scEqSpine (sp :< x) (sp' :< y)
    = do x' <- value x
         y' <- value y
         if !(sizeEq x' y')
            then scEqSpine sp sp'
            else pure False
scEqSpine _ _ = pure False

-- Approximate equality between values. We don't go under binders - we're
-- only checking for size change equality so expect to just see type and
-- data constructors
-- TODO: size change for pattern matching on types
sizeEq' : Value f vars -> Value f' vars -> Core Bool
-- Should never see this since we always call with vars = [<], but it is
-- technically possible
sizeEq' (VLocal _ idx _ sp) (VLocal _ idx' _ sp')
    = if idx == idx'
         then scEqSpine sp sp'
         else pure False
sizeEq' (VMeta{}) _ = pure True
sizeEq' _ (VMeta{}) = pure True
-- sizeEq' (VMeta _ _ i _ args _) (VMeta _ _ i' _ args' _)
--    -- = i == i' && assert_total (all (uncurry sizeEq) (zip args args'))
--    = if i /= i' then pure False
--      else pure $ assert_total
--        !(allM (uncurry sizeEq) !paired_values)
--    where
--      paired_values : Core (SnocList (Value Glue vars, Value Glue vars))
--      paired_values = traverse (\(a, a') => pure (!a, !a')) (zip (map value args) (map value args'))
sizeEq' (VApp _ _ n sp _) (VApp _ _ n' sp' _)
    = if n == n'
         then scEqSpine sp sp'
         else pure False
sizeEq' (VDCon _ _ t a sp) (VDCon _ _ t' a' sp')
    = if t == t'
         then scEqSpine sp sp'
         else pure False
sizeEq' (VTCon _ n a sp) (VTCon _ n' a' sp')
    = if n == n'
         then scEqSpine sp sp'
         else pure False
sizeEq' (VAs _ _ a p) p' = sizeEq p p'
sizeEq' p (VAs _ _ a p') = pure $ !(sizeEq p a) || !(sizeEq p p')
sizeEq' (VDelayed _ _ t) (VDelayed _ _ t') = sizeEq t t'
sizeEq' (VDelay _ _ t x) (VDelay _ _ t' x')
     = if !(sizeEq t t') then sizeEq x x'
          else pure False
sizeEq' (VForce _ _ t [<]) (VForce _ _ t' [<]) = sizeEq t t'
sizeEq' (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
-- -- traverse dotted LHS terms
-- sizeEq' t (VErased _ (Dotted t')) =
--   -- eqTerm t t'
--   sizeEq t t' -- t' is no longer a pattern
sizeEq' (VErased _ _) (VErased _ _) = pure True
sizeEq' (VUnmatched _ _) (VUnmatched _ _) = pure True
sizeEq' (VType _ _) (VType _ _) = pure True
sizeEq' _ _ = pure False -- other cases not checkable

-- Drop any non-inf top level laziness annotations
-- Remove all force and delay annotations which are nothing to do with
-- coinduction meaning that all Delays left guard coinductive calls.
delazy : Value f vars -> Core (Glued vars)
delazy val@(VDelayed _ r t)
    = case r of
           LInf => pure (asGlued val)
           _ => pure t
delazy val@(VDelay _ r t v)
    = case r of
           LInf => pure (asGlued val)
           _ => pure v
delazy val@(VForce fc r v sp)
    = case r of
           LInf => pure (asGlued val)
           _ => applyAll fc v (cast (map (\ e => (multiplicity e, value e)) sp))
delazy val = pure (asGlued val)

sizeEq x y = sizeEq' !(delazy x) !(delazy y)

mutual
  findSC : {auto c : Ref Ctxt Defs} ->
           {auto v : Ref SCVar Int} ->
           Guardedness ->
           ForcedEqs ->
           List (Glued [<]) -> -- LHS args and their position
           Glued [<] -> -- definition. No expanding to NF, we want to check
                        -- the program as written (plus tcinlines)
           Core (List SCCall)
  findSC g eqs args (VBind fc n b sc)
      = do v <- nextVar
           pure $ !(findSCbinder b) ++ !(findSC g eqs args !(sc (pure v)))
    where
        findSCbinder : Binder (Glued [<]) -> Core (List SCCall)
        findSCbinder (Let _ c val ty) = findSC g eqs args val
        findSCbinder _ = pure [] -- only types, no need to look
  -- If we're Guarded and find a Delay, continue with the argument as InDelay
  findSC Guarded eqs pats (VDelay _ LInf _ tm)
      = findSC InDelay eqs pats tm
  findSC g eqs pats (VDelay _ _ _ tm)
      = findSC g eqs pats tm
  findSC g eqs pats (VForce _ _ v sp)
      = do vCalls <- findSC g eqs pats v
           spCalls <- findSCspine Unguarded eqs pats sp
           pure (vCalls ++ spCalls)
  findSC g eqs args (VCase fc ct c (VApp _ Bound n [<] _) scTy alts)
      = do altCalls <- traverse (findSCalt g eqs args (Just n)) alts
           pure (concat altCalls)
  findSC g eqs args (VCase fc ct c sc scTy alts)
      = do altCalls <- traverse (findSCalt g eqs args Nothing) alts
           scCalls <- findSC Unguarded eqs args (asGlued sc)
           pure (scCalls ++ concat altCalls)
  findSC g eqs pats tm = findSCapp g eqs pats tm

  findSCapp : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
              Guardedness ->
              ForcedEqs ->
              List (Glued [<]) -> -- LHS args and their position
              Glued [<] -> -- dealing with cases where this is an application
                           -- of some sort
              Core (List SCCall)
  findSCapp g eqs pats (VLocal fc _ _ sp)
      = do args <- traverseSnocList value sp
           scs <- traverseSnocList (findSC g eqs pats) args
           pure (concat scs)
  findSCapp g eqs pats (VApp fc Bound _ sp _)
      = do args <- traverseSnocList value sp
           scs <- traverseSnocList (findSC g eqs pats) args
           pure (concat scs)
  findSCapp g eqs pats (VApp fc Func fn sp _)
      = do defs <- get Ctxt
           args <- traverseSnocList value sp
           Just ty <- lookupTyExact fn (gamma defs)
              | Nothing => do
                  log "totality" 50 $ "Lookup failed"
                  findSCcall Unguarded eqs pats fc fn (cast args)
           allg <- allGuarded fn
           -- If it has the all guarded flag, pretend it's a data constructor
           -- Otherwise just carry on as normal
           if allg
              then findSCapp g eqs pats (VDCon fc fn 0 0 sp)
              else case g of
                      -- constructor guarded and delayed, so just check the
                      -- arguments
                      InDelay => findSCspine Unguarded eqs pats sp
                      _ => findSCcall Unguarded eqs pats fc fn (cast args)
    where
      allGuarded : Name -> Core Bool
      allGuarded n
          = do defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                    | Nothing => pure False
               pure (AllGuarded `elem` flags gdef)
    -- If we're InDelay and find a constructor (or a function call which is
    -- guaranteed to return a constructor; AllGuarded set), continue as InDelay
  findSCapp InDelay eqs pats (VDCon fc n t a sp)
      = findSCspine InDelay eqs pats sp
  findSCapp Guarded eqs pats (VDCon fc n t a sp)
      = do defs <- get Ctxt
           Just ty <- lookupTyExact n (gamma defs)
                | Nothing => do
                     log "totality" 50 $ "Lookup failed"
                     findSCcall Guarded eqs pats fc n (toList !(traverseSnocList value sp))
           findSCcall Guarded eqs pats fc n (toList !(traverseSnocList value sp))
  findSCapp Toplevel eqs pats (VDCon fc n t a sp)
      = do defs <- get Ctxt
           Just ty <- lookupDefExact n (gamma defs)
                | Nothing => do
                     log "totality" 50 $ "Lookup failed"
                     findSCcall Guarded eqs pats fc n (toList !(traverseSnocList value sp))
           findSCcall Guarded eqs pats fc n (toList !(traverseSnocList value sp))
  findSCapp g eqs pats tm = pure [] -- not an application (TODO: VTCon)

  findSCscope : {auto c : Ref Ctxt Defs} ->
                {auto v : Ref SCVar Int} ->
                Guardedness ->
                ForcedEqs ->
                List (Glued [<]) -> -- LHS args and their position
                Maybe Name -> -- variable we're splitting on (if it is a variable)
                FC -> Glued [<] ->
                (args : _) -> VCaseScope args [<] -> -- case alternative
                Core (List SCCall)
  findSCscope g eqs args var fc pat [<] sc
     = do (eqsc, rhs) <- sc
          logC "totality.termination.sizechange" 10 $
              (do tms <- traverse (\ (gx, gy) =>
                              pure (!(toFullNames !(quote [<] gx)),
                                    !(toFullNames !(quote [<] gy)))) eqsc
                  pure ("Force equalities " ++ show tms))
          let eqs' = eqsc ++ eqs
          args' <- maybe (pure args) (\v => replaceInArgs v pat args) var
          logNF "totality.termination.sizechange" 10 "RHS for \{show !(toFullNames var)}" [<] rhs
          logC "totality.termination.sizechange" 10 $
              do pat' <- toFullNames !(quote [<] pat)
                 targs <- traverse (\t => toFullNames !(quote [<] t)) args
                 targs' <- traverse (\t => toFullNames !(quote [<] t)) args'
                 pure ("Pat \{show pat'}, args: \{show targs}, args': \{show targs'}")

          findSC g eqs'
                 !(traverse (\ arg => pure !(canonicalise eqs' arg)) args')
                 rhs
  findSCscope g eqs args var fc pat (cargs :< (c, xn)) sc
     = do varg <- nextVar
          pat' <- the (Core (Glued [<])) $ case pat of
                    VDCon vfc n t a sp =>
                        pure (VDCon vfc n t a (sp :< MkSpineEntry fc c (pure varg)))
                    _ => throw (InternalError "Not a data constructor in findSCscope")
          findSCscope g eqs args var fc pat' cargs (sc (pure varg))


  findSCalt : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
              Guardedness ->
              ForcedEqs ->
              List (Glued [<]) -> -- LHS args and their position
              Maybe Name -> -- variable we're splitting on (if it is a variable)
              VCaseAlt [<] -> -- case alternative
              Core (List SCCall)
  findSCalt g eqs args var (VConCase fc n t cargs sc)
      = findSCscope g eqs args var fc (VDCon fc n t (length cargs) [<]) _ sc
  findSCalt g eqs args var (VDelayCase fc ty arg tm)
      = do targ <- nextVar
           varg <- nextVar
           let pat = VDelay fc LUnknown targ varg
           (eqs, rhs) <- tm (pure targ) (pure varg)
           findSC g eqs !(expandForced eqs
                       !(maybe (pure args)
                               (\v => replaceInArgs v pat args) var))
                    rhs
  findSCalt g eqs args var (VConstCase fc c tm)
      = findSC g eqs !(maybe (pure args)
                         (\v => replaceInArgs v (VPrimVal fc c) args) var)
                 tm
  findSCalt g eqs args var (VDefaultCase fc tm) = findSC g eqs args tm


  findSCspine : {auto c : Ref Ctxt Defs} ->
           {auto v : Ref SCVar Int} ->
           Guardedness ->
           ForcedEqs ->
           List (Glued [<]) -> -- LHS args and their position
           Spine [<] ->
           Core (List SCCall)
  findSCspine g eqs pats [<] = pure []
  findSCspine g eqs pats (sp :< e)
      = do vCalls <- findSC g eqs pats !(value e)
           spCalls <- findSCspine g eqs pats sp
           pure (vCalls ++ spCalls)

  knownOr : Core SizeChange -> Core SizeChange -> Core SizeChange
  knownOr x y = case !x of Unknown => y; _ => x

  plusLazy : Core SizeChange -> Core SizeChange -> Core SizeChange
  plusLazy x y = case !x of Smaller => pure Smaller; x => pure $ x |+| !y

  -- Return whether first argument is structurally smaller than the second.
  sizeCompare : {auto c : Ref Ctxt Defs} ->
                {auto defs : Defs} ->
                Nat -> -- backtracking fuel
                Glued [<] -> -- RHS: term we're checking
                Glued [<] -> -- LHS: argument it might be smaller than
                Core SizeChange

  sizeCompareCon : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> Glued [<] -> Core Bool
  sizeCompareTyCon : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> Glued [<] -> Core Bool
  sizeCompareConArgs : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> List (Glued [<]) -> Core Bool
  sizeCompareApp : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Glued [<] -> Glued [<] -> Core SizeChange

--   sizeCompare fuel s (VErased _ (Dotted t)) = sizeCompare fuel s t
  sizeCompare fuel _ (VErased _ _) = pure Unknown -- incomparable!
  -- for an as pattern, it's smaller if it's smaller than either part
  sizeCompare fuel s (VAs _ _ p t)
      = knownOr (sizeCompare fuel s p) (sizeCompare fuel s t)
  sizeCompare fuel (VAs _ _ p s) t
      = knownOr (sizeCompare fuel p t) (sizeCompare fuel s t)
--   -- if they're both metas, let sizeEq check if they're the same
--   sizeCompare fuel s@(VMeta _ _ _ _ _ _) t@(VMeta _ _ _ _ _ _) = pure (if !(sizeEq s t) then Same else Unknown)
--   -- otherwise try to expand RHS meta
--   sizeCompare fuel s@(VMeta _ n i args _ _) t = do
--     Just gdef <- lookupCtxtExact (Resolved i) (gamma defs) | _ => pure Unknown
--     let (Function _ tm _ _) = definition gdef | _ => pure Unknown
--     tm <- substMeta tm !(traverse snd args) zero [<]
--     sizeCompare fuel tm t
--     where
--       substMeta : {0 drop : _} ->
--                   Term ([<] ++ drop) -> List (Glued [<]) ->
--                   SizeOf drop -> Subst Glued drop [<] ->
--                   Core (Glued [<])
--       substMeta (Bind bfc n (Lam _ c e ty) sc) (a :: as) drop env
--           = substMeta sc as (suc drop) (env :< a)
--       substMeta (Bind bfc n (Let _ c val ty) sc) as drop env
--           = substMeta (subst val sc) as drop env
--       substMeta rhs [] drop env = (nf [<] (substs drop !(to_env env) rhs))
--         where
--           to_env : {0 drop : _} -> Subst Glued drop [<] -> Core (Subst Term drop [<])
--           to_env [<] = pure [<]
--           to_env (as :< a) = pure $ !(to_env as) :< !(quote [<] a)
--       substMeta rhs _ _ _ = throw (InternalError ("Badly formed metavar solution \{show n}"))

  sizeCompare fuel s t
        = if !(sizeCompareCon fuel s t)
            then pure Smaller
            else knownOr (sizeCompareApp fuel s t) (pure $ if !(sizeEq s t) then Same else Unknown)
    --  = if !(sizeCompareTyCon fuel s t) then pure Same
    --    else if !(sizeCompareCon fuel s t)
    --       then pure Smaller
    --       else knownOr (sizeCompareApp fuel s t) (pure $ if !(sizeEq s t) then Same else Unknown)

  sizeCompareProdConArgs : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> List (Glued [<]) -> List (Glued [<]) -> Core SizeChange
  sizeCompareProdConArgs _ [] [] = pure Same
  sizeCompareProdConArgs fuel (x :: xs) (y :: ys) =
    case !(sizeCompare fuel x y) of
      Unknown => pure Unknown
      t => (t |*|) <$> sizeCompareProdConArgs fuel xs ys
  sizeCompareProdConArgs _ _ _ = pure Unknown

  sizeCompareTyCon fuel s t =
    case t of
      VTCon _ cn _ args => case s of
        VTCon _ cn' _ args' => if cn == cn'
            then (Unknown /=) <$> sizeCompareProdConArgs fuel (toList !(traverseSnocList value args')) (toList !(traverseSnocList value args))
            else pure False
        _ => pure False
      _ => pure False

  sizeCompareCon fuel s t
      = case t of
             VDCon _ cn _ _ sp =>
                do
                    sp_value <- toList <$> traverseSnocList value sp
                    sizeCompareConArgs (minus fuel 1) s sp_value
             _ => pure False

            --  VDCon _ cn _ _ sp =>
            --   do
            --     sp_value <- toList <$> traverseSnocList value sp
            --     -- if s is smaller or equal to an arg, then it is smaller than t
            --     if !(sizeCompareConArgs (minus fuel 1) s sp_value) then pure True
            --      else case (fuel, s) of
            --             (S k, VDCon _ cn' _ _ sp') => do
            --                     -- if s is a matching DataCon, applied to same number of args,
            --                     -- no Unknown args, and at least one Smaller
            --                     if cn == cn' && length sp == length sp'
            --                       then (Smaller ==) <$> sizeCompareProdConArgs k (toList !(traverseSnocList value sp')) sp_value
            --                       else pure False
            --             _ => pure $ False
            --  _ => pure False

  sizeCompareConArgs _ s [] = pure False
  sizeCompareConArgs fuel s (t :: ts)
      = case !(sizeCompare fuel s t) of
          Unknown => sizeCompareConArgs fuel s ts
          _ => pure True

  sizeCompareApp fuel (VApp fc nt n sp@(_ :< _) _) tm = sizeCompare fuel (VApp fc nt n [<] (pure Nothing)) tm
  sizeCompareApp _ _ t = pure Unknown

  sizeCompareAsserted : {auto c : Ref Ctxt Defs} -> {auto defs : Defs} -> Nat -> Maybe (Glued [<]) -> Glued [<] -> Core SizeChange
  sizeCompareAsserted fuel (Just s) t
      = pure $ case !(sizeCompare fuel s t) of
          Unknown => Unknown
          _ => Smaller
  sizeCompareAsserted _ Nothing _ = pure Unknown

  -- if the argument is an 'assert_smaller', return the thing it's smaller than
  asserted : ForcedEqs -> Name -> Glued [<] -> Core (Maybe (Glued [<]))
  asserted eqs aSmaller (VApp _ nt fn [<_, _, e, _] _)
       = if fn == aSmaller
            then Just <$> canonicalise eqs !(value e)
            else pure Nothing
  asserted _ _ _ = pure Nothing

  -- Calculate the size change for the given argument.
  -- i.e., return the size relationship of the given argument with an entry
  -- in 'pats'; the position in 'pats' and the size change.
  -- Nothing if there is no relation with any of them.
  mkChange : {auto c : Ref Ctxt Defs} ->
             ForcedEqs ->
             Name ->
             (pats : List (Glued [<])) ->
             (arg : Glued [<]) ->
             Core (List SizeChange)
  mkChange eqs aSmaller pats arg
    = do defs <- get Ctxt
         -- logC "totality.termination.sizechange" 10 $ do pure "mkChange pats: \{show pats}"
         let fuel = defs.options.elabDirectives.totalLimit
         traverse (\p => plusLazy (sizeCompareAsserted fuel !(asserted eqs aSmaller arg) p) (sizeCompare fuel arg p)) pats

  findSCcall : {auto c : Ref Ctxt Defs} ->
               {auto v : Ref SCVar Int} ->
               Guardedness ->
               ForcedEqs ->
               List (Glued [<]) ->
               FC -> Name -> List (Glued [<]) ->
               Core (List SCCall)
  findSCcall g eqs pats fc fn_in args
          -- Under 'assert_total' we assume that all calls are fine, so leave
          -- the size change list empty
        = do args <- traverse (canonicalise eqs) args
             defs <- get Ctxt
             fn <- getFullName fn_in
             logC "totality.termination.sizechange" 10 $ do pure "Looking under \{show fn}"
             aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
             logC "totality.termination.sizechange" 10 $
                 do under <- traverse (\t => toFullNames !(quote [<] t)) pats -- hang at quoteNF
                    targs <- traverse (\t => toFullNames !(quote [<] t)) args -- hang at quoteNF
                    pure ("Under " ++ show under ++ "\n" ++ "Args " ++ show targs)
             if fn == NS builtinNS (UN $ Basic "assert_total")
                then pure []
                else
                 do scs <- traverse (findSC g eqs pats) args
                    pure ([MkSCCall fn
                             (fromListList
                                  !(traverse (mkChange eqs aSmaller pats) args))
                             fc]
                             ++ concat scs)

findSCTop : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
            List (Glued [<]) -> Glued [<] -> Core (List SCCall)
findSCTop args (VBind _ _ (Lam _ _ _ _) sc)
    = do arg <- nextVar
         findSCTop (arg :: args) !(sc $ pure arg)
findSCTop args def
    = do for_ args $ \arg => do
            logNF "totality.termination.sizechange" 10 "From tree arg: " [<] arg

         findSC Toplevel [] (reverse args) def

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ tm _ _)
   = do ntm <- nfTotality [<] tm
        logNF "totality.termination.sizechange" 5 "From tree" [<] ntm
        v <- newRef SCVar 0
        sc <- findSCTop [] ntm
        pure $ nub sc
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do logC "totality.termination.sizechange" 5 $ do pure $ "Calculating Size Change: " ++ show !(toFullNames n)
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         r <- getSC defs (definition def)
         log "totality.termination.sizechange" 5 $ "Calculated: " ++ show r
         pure r
