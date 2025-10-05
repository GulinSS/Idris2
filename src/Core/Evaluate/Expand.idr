module Core.Evaluate.Expand

import Core.Context
import Core.Env
import Core.Context.Log
import Core.Evaluate.Value
import Core.Primitives
import Core.Evaluate.Quote

import Data.Vect
import Data.SnocList
import Libraries.Data.WithDefault

data ExpandMode
  = Resolved -- all resolved names (and names w/o a namespace) will be treated as safe to expand
             -- (regardless their actual visibility)
  | Cases -- look into top level cases

Show ExpandMode where
  show Resolved = "Resolved"
  show Cases = "Cases"

Eq ExpandMode where
  (==) Resolved Resolved = True
  (==) Cases Cases = True
  (==) _ _ = False

Ord ExpandMode where
  compare Resolved Resolved = EQ
  compare Resolved _ = LT
  compare _ Resolved = GT
  compare Cases Cases = EQ

-- If a value is an App or Meta node, then it might be reducible. Expand it
-- just enough that we have the right top level node.
-- Don't expand Apps to a blocked top level cases, unless 'cases' is set.
-- The 'believe_me' are there to save us deconstructing and reconstructing
-- just to change a compile-time only index
expand' : {auto c : Ref Ctxt Defs} ->
          {vars: _} ->
          ExpandMode -> Value f vars -> Core (NF vars)
expand' mode v@(VApp fc nt n sp val)
    = do vis <- getVisibilityWeaked fc n
         m_mult <- getMultiplicityWeaked fc n
         full_name <- toFullNames n
         defs <- get Ctxt
         let ns = currentNS defs :: nestedNS defs
         logC "eval.def.stuck" 50 $ pure "expand App \{show mode} ns: \{show ns}, n: \{show n}, vis: \{show $ collapseDefault vis}, mult: \{show m_mult}, full_name: \{show full_name}"
         if reducibleInAny ns n (collapseDefault vis)
            then do
               Just val' <- logDepth val
                    | Nothing => pure (believe_me v)
               logC "eval.def.stuck" 50 $ do val' <- toFullNames val'
                                             pure "Reduced \{show full_name} to \{show val'}"
               if mode >= Cases
                  then expand' mode val'
                  else if !(blockedApp val')
                          then pure (believe_me v)
                          else expand' mode val'
            else pure (believe_me v)
  where
    blockedApp : forall f . Value f vars -> Core Bool
    blockedApp (VBind fc _ (Lam {}) sc)
        = blockedApp !(sc $ pure $ VErased fc Placeholder)
    blockedApp (VCase _ PatMatch _ _ _ _) = pure True
    blockedApp (VPrimOp{}) = pure True
    blockedApp _ = pure False

expand' mode (VErased fc (Dotted t))
    = do t' <- expand' mode t
         pure (VErased fc (Dotted t'))
expand' mode v@(VMeta fc n i args sp val)
    = do logC "eval.def.stuck" 50 $ pure "expand Meta n: \{show n}"
         Just val' <- logDepth val
              | Nothing => pure (believe_me v)
         logC "eval.def.stuck" 50 $ do n' <- toFullNames n
                                       val' <- toFullNames val'
                                       pure "Reduced \{show n'} to \{show val'}"
         expand' mode val'
expand' mode val = pure (believe_me val)

logNF : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        LogTopic -> Nat -> Lazy String -> Value f vars -> Core ()
logNF s n msg tmnf
    = when !(logging s n) $
        do defs <- get Ctxt
           tm <- logQuiet $ quote (mkEnv emptyFC _) tmnf
           tm' <- toFullNames tm
           depth <- getDepth
           logString depth s.topic n (msg ++ ": " ++ show tm')

export
expand : {auto c : Ref Ctxt Defs} ->
         {vars: _} ->
         Value f vars -> Core (NF vars)
expand v = do
  logNF "eval.def.stuck" 50 "Begin Expand Resolved for" v
  logDepth $ expand' Resolved v

export
expandCases : {auto c : Ref Ctxt Defs} ->
             {vars: _} ->
             Value f vars -> Core (NF vars)
expandCases v = do
  logNF "eval.def.stuck" 50 "Begin Expand Cases for" v
  logDepth $ expand' Cases v

export
spineVal : {auto c : Ref Ctxt Defs} ->
           {vars: _} ->
           SpineEntry vars -> Core (NF vars)
spineVal e = expand !(value e)
