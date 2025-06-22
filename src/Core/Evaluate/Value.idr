module Core.Evaluate.Value

import Core.Context
import Core.Core
import Core.TT

import Data.SnocList
import Data.Vect

import Libraries.Data.WithDefault

-- public export
-- data EvalOrder = CBV | CBN

-- public export
-- record EvalOpts where
--   constructor MkEvalOpts
--   holesOnly : Bool -- only evaluate hole solutions
--   argHolesOnly : Bool -- only evaluate holes which are relevant arguments
--   removeAs : Bool -- reduce 'as' patterns (don't do this on LHS)
--   evalAll : Bool -- evaluate everything, including private names
--   tcInline : Bool -- inline for totality checking
--   fuel : Maybe Nat -- Limit for recursion depth
--   reduceLimit : List (Name, Nat) -- reduction limits for given names. If not
--                      -- present, no limit
--   strategy : EvalOrder

-- export
-- defaultOpts : EvalOpts
-- defaultOpts = MkEvalOpts False False True False False Nothing [] CBN

-- export
-- withHoles : EvalOpts
-- withHoles = MkEvalOpts True True False False False Nothing [] CBN

-- export
-- withAll : EvalOpts
-- withAll = MkEvalOpts False False True True False Nothing [] CBN

-- export
-- withArgHoles : EvalOpts
-- withArgHoles = MkEvalOpts False True False False False Nothing [] CBN

-- export
-- tcOnly : EvalOpts
-- tcOnly = { tcInline := True } withArgHoles

-- export
-- onLHS : EvalOpts
-- onLHS = { removeAs := False } defaultOpts

-- export
-- cbn : EvalOpts
-- cbn = defaultOpts

-- export
-- cbv : EvalOpts
-- cbv = { strategy := CBV } defaultOpts


public export
data Form = Glue | Normal

public export
data Value : Form -> SnocList Name -> Type

public export
Glued : SnocList Name -> Type
Glued = Value Glue

public export
NF : SnocList Name -> Type
NF = Value Normal

public export
ClosedNF : Type
ClosedNF = NF [<]

public export
data VCaseAlt : SnocList Name -> Type

public export
record SpineEntry vars where
  constructor MkSpineEntry
  loc : FC
  multiplicity : RigCount
  value : Core (Glued vars)

public export
0 Spine : SnocList Name -> Type
Spine vars = SnocList (SpineEntry vars)

-- The 'Form' is a phantom type index that says whether we know the value is
-- in normal form, or whether it might be 'Glued'
-- In theory, we know that everything except 'VApp' and "VMeta' are Normal,
-- but in practice this is annoying because evaluating doesn't know whether
-- it's going to produce a 'Glued' or a 'Normal'.
-- The phantom index gives us enough help, specifically in that it means we
-- are sure that we've expanded to head normal Normal form before processing
-- a Value
public export
data Value : Form -> SnocList Name -> Type where
     VBind : FC -> (x : Name) -> Binder (Glued vars) ->
             (sc : Core (Glued vars) -> Core (Glued vars)) ->
             Value f vars
     -- A 'glued' application. This includes the original application
     -- (for quoting back HNFs) and what it reduces to (if the name is
     -- defined).
     VApp : FC ->
            NameType -> Name -> Spine vars -> -- original form
            Core (Maybe (Glued vars)) -> -- the normal form
            Value f vars
     VLocal   : FC -> (idx : Nat) -> (0 p : IsVar n idx vars) ->
                Spine vars ->
                Value f vars
     VMeta  : FC -> Name -> Int -> -- Name and resolved name of metavar
              List (RigCount, Core (Glued vars)) -> -- Scope of metavar
              Spine vars ->
              Core (Maybe (Glued vars)) -> -- the normal form, if solved
              Value f vars
     VDCon    : FC -> Name -> (tag : Tag) -> (arity : Nat) ->
                Spine vars -> Value f vars
     VTCon    : FC -> Name -> (arity : Nat) ->
                Spine vars -> Value f vars
     VAs      : FC -> UseSide -> Value f vars -> Value f vars -> Value f vars
     VCase    : FC -> CaseType ->
                RigCount -> (sc : NF vars) -> (scTy : Glued vars) ->
                List (VCaseAlt vars) ->
                Value f vars
     VDelayed : FC -> LazyReason -> Glued vars -> Value f vars
     VDelay   : FC -> LazyReason -> Glued vars -> Glued vars -> Value f vars
     VForce   : FC -> LazyReason -> Glued vars -> Spine vars -> Value f vars
     VPrimVal : FC -> Constant -> Value f vars
     VPrimOp  : {ar : _} ->
                FC -> PrimFn ar -> Vect ar (Glued vars) -> Value f vars
     VErased  : FC -> WhyErased (Value f vars) -> Value f vars
     VUnmatched : FC -> String -> Value f vars
     VType    : FC -> Name -> Value f vars

export
vRef : FC -> NameType -> Name -> Value f vars
vRef fc nt n = VApp fc nt n [<] (pure Nothing)

export
getLoc : Value f vars -> FC
getLoc (VBind fc x y sc) = fc
getLoc (VApp fc x y sx z) = fc
getLoc (VLocal fc idx p sx) = fc
getLoc (VMeta fc x y xs sx z) = fc
getLoc (VDCon fc x tag arity sx) = fc
getLoc (VTCon fc x arity sx) = fc
getLoc (VAs fc x y z) = fc
getLoc (VCase fc t x sc scTy xs) = fc
getLoc (VDelayed fc x y) = fc
getLoc (VDelay fc x y z) = fc
getLoc (VForce fc x y sx) = fc
getLoc (VPrimVal fc x) = fc
getLoc (VPrimOp fc x xs) = fc
getLoc (VErased fc imp) = fc
getLoc (VUnmatched fc x) = fc
getLoc (VType fc x) = fc

-- If a value is an App or Meta node, then it might be reducible. Expand it
-- just enough that we have the right top level node.
-- Don't expand Apps to a blocked top level cases, unless 'cases' is set.
-- The 'believe_me' are there to save us deconstructing and reconstructing
-- just to change a compile-time only index
expand' : {auto c : Ref Ctxt Defs} ->
          Bool -> Value f vars -> Core (NF vars)
expand' cases v@(VApp fc nt n sp val)
    = do vis <- getVisibilityWeaked fc n
         defs <- get Ctxt
         let ns = currentNS defs :: nestedNS defs
         if reducibleInAny ns n (collapseDefault vis)
            then do
               Just val' <- val
                    | Nothing => pure (believe_me v)
               if cases
                  then expand' cases val'
                  else if !(blockedApp val')
                          then pure (believe_me v)
                          else expand' cases val'
            else pure (believe_me v)
  where
    blockedApp : forall f . Value f vars -> Core Bool
    blockedApp (VBind fc _ (Lam {}) sc)
        = blockedApp !(sc $ pure $ VErased fc Placeholder)
    blockedApp (VCase _ PatMatch _ _ _ _) = pure True
    blockedApp (VPrimOp{}) = pure True
    blockedApp _ = pure False

expand' cases v@(VMeta fc n i args sp val)
    = do Just val' <- val
              | Nothing => pure (believe_me v)
         expand' cases val'
expand' cases val = pure (believe_me val)

export
expand : {auto c : Ref Ctxt Defs} ->
         Value f vars -> Core (NF vars)
expand = expand' False

export
expandFull : {auto c : Ref Ctxt Defs} ->
             Value f vars -> Core (NF vars)
expandFull = expand' True

-- It's safe to pretend an NF is Glued, if we need it
export
asGlued : Value f vars -> Glued vars
asGlued = believe_me -- justification as above

export
spineVal : {auto c : Ref Ctxt Defs} ->
           SpineEntry vars -> Core (NF vars)
spineVal e = expand !(value e)

public export
0 VCaseScope : SnocList (RigCount, Name) -> SnocList Name -> Type
VCaseScope [<] vars = Core (List (Glued vars, Glued vars), Glued vars)
VCaseScope (xs :< x) vars = Core (Glued vars) -> VCaseScope xs vars

public export
data VCaseAlt : SnocList Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     VConCase : FC -> Name -> (tag : Int) ->
                (args : SnocList (RigCount, Name)) ->
                VCaseScope args vars -> VCaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     VDelayCase : FC -> (ty : Name) -> (arg : Name) ->
                  VCaseScope [<(Algebra.Preorder.top, arg), (Algebra.Semiring.erased, ty)] vars ->
                  VCaseAlt vars
     ||| Match against a literal
     VConstCase : FC -> Constant -> Glued vars -> VCaseAlt vars
     ||| Catch-all case
     VDefaultCase : FC -> Glued vars -> VCaseAlt vars

-- Show what form a value has, for debugging
export
qshow : Value f vars -> String
qshow (VBind{}) = "Bind"
qshow (VApp _ _ n _ _) = "App " ++ show n
qshow (VLocal{}) = "Local"
qshow (VMeta _ n _ _ _ _) = "Meta " ++ show n
qshow (VDCon _ n _ _ _) = "DCon " ++ show n
qshow (VTCon _ n _ _) = "TCon " ++ show n
qshow (VCase{}) = "Case"
qshow (VPrimVal _ c) = "Constant " ++ show c
qshow (VPrimOp _ f args) = "PrimOp " ++ show f ++ " " ++ show (length args)
qshow _ = "???"

-- export
-- HasNames (NHead free) where
--   full defs (NRef nt n) = NRef nt <$> full defs n
--   full defs hd = pure hd

--   resolved defs (NRef nt n) = NRef nt <$> resolved defs n
--   resolved defs hd = pure hd

-- export
-- HasNames (NCaseAlt free)

-- export
-- HasNames (NF free) where
--   full defs (NBind fc x bd f) = pure $ NBind fc x bd f
--   full defs (NApp fc hd xs) = pure $ NApp fc !(full defs hd) xs
--   full defs (NDCon fc n tag arity xs) = pure $ NDCon fc !(full defs n) tag arity xs
--   full defs (NTCon fc n tag arity xs) = pure $ NTCon fc !(full defs n) tag arity xs
--   full defs (NAs fc side nf nf1) = pure $ NAs fc side !(full defs nf) !(full defs nf1)
--   full defs (NCase fc ct rc sc scTy alts) = pure $ NCase fc ct rc !(full defs sc) scTy !(traverse (full defs) alts)
--   full defs (NDelayed fc lz nf) = pure $ NDelayed fc lz !(full defs nf)
--   full defs (NDelay fc lz cl cl1) = pure $ NDelay fc lz cl cl1
--   full defs (NForce fc lz nf xs) = pure $ NForce fc lz !(full defs nf) xs
--   full defs (NPrimVal fc cst) = pure $ NPrimVal fc cst
--   full defs (NPrimOp fc op args) = pure $ NPrimOp fc op !(traverseVect (full defs) args)
--   full defs (NErased fc imp) = pure $ NErased fc imp
--   full defs (NUnmatched fc n) = pure $ NUnmatched fc n
--   full defs (NType fc n) = pure $ NType fc !(full defs n)

--   resolved defs (NBind fc x bd f) = pure $ NBind fc x bd f
--   resolved defs (NApp fc hd xs) = pure $ NApp fc !(resolved defs hd) xs
--   resolved defs (NDCon fc n tag arity xs) = pure $ NDCon fc !(resolved defs n) tag arity xs
--   resolved defs (NTCon fc n tag arity xs) = pure $ NTCon fc !(resolved defs n) tag arity xs
--   resolved defs (NAs fc side nf nf1) = pure $ NAs fc side !(resolved defs nf) !(resolved defs nf1)
--   resolved defs (NCase fc ct rc sc scTy alts) = pure $ NCase fc ct rc !(resolved defs sc) scTy !(resolved defs alts)
--   resolved defs (NDelayed fc lz nf) = pure $ NDelayed fc lz !(resolved defs nf)
--   resolved defs (NDelay fc lz cl cl1) = pure $ NDelay fc lz cl cl1
--   resolved defs (NForce fc lz nf xs) = pure $ NForce fc lz !(resolved defs nf) xs
--   resolved defs (NPrimVal fc cst) = pure $ NPrimVal fc cst
--   resolved defs (NPrimOp fc op args) = pure $ NPrimOp fc op !(traverseVect (resolved defs) args)
--   resolved defs (NErased fc imp) = pure $ NErased fc imp
--   resolved defs (NUnmatched fc n) = pure $ NUnmatched fc n
--   resolved defs (NType fc n) = pure $ NType fc !(resolved defs n)

-- export
-- HasNames (NCaseAlt free) where
--   full defs (NConCase fc n tag args cl) = pure $ NConCase fc !(full defs n) tag args cl
--   full defs (NDelayCase fc n arg cl) = pure $ NDelayCase fc !(full defs n) arg cl
--   full defs (NConstCase fc c cl) = pure $ NConstCase fc c cl
--   full defs (NDefaultCase fc cl) = pure $ NDefaultCase fc cl

--   resolved defs (NConCase fc n tag args cl) = pure $ NConCase fc !(resolved defs n) tag args cl
--   resolved defs (NDelayCase fc n arg cl) = pure $ NDelayCase fc !(resolved defs n) arg cl
--   resolved defs (NConstCase fc c cl) = pure $ NConstCase fc c cl
--   resolved defs (NDefaultCase fc cl) = pure $ NDefaultCase fc cl

-- mutual
--   export
--   covering
--   {free : _} -> Show (NHead free) where
--     show (NLocal _ idx p) = show (nameAt p) ++ "[" ++ show idx ++ "]"
--     show (NRef _ n) = show n
--     show (NMeta n _ args) = "?" ++ show n ++ "_[" ++ show (length args) ++ " closures " ++ showClosureSnocList (map ((emptyFC,) . snd) args) ++ "]"

--   export
--   covering
--   {free : _} -> Show (Closure free) where
--     show (MkClosure _ _ _ tm) = "[closure] MkClosure: " ++ show tm
--     show (MkNFClosure _ _ tm) = "[closure] MkNFClosure: " ++ show tm

--   export
--   covering
--   showClosureSnocList : {free : _} -> SnocList (FC, Closure free) -> String
--   showClosureSnocList xs = concat ("[" :: intersperse ", " (show' [] xs) ++ ["]"])
--     where
--       show' : List String -> SnocList (FC, Closure free) -> List String
--       show' acc Lin       = acc
--       show' acc (xs :< (_, x)) = show' (show x :: acc) xs

--   export
--   covering
--   {free : _} -> Show (NF free) where
--     show (NBind _ x (Lam _ c info ty) _)
--       = "\\" ++ withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
--         " => [closure]"
--     show (NBind _ x (Let _ c val ty) _)
--       = "let " ++ showCount c ++ show x ++ " : " ++ show ty ++
--         " = " ++ show val ++ " in [closure]"
--     show (NBind _ x (Pi _ c info ty) _)
--       = withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
--         " -> [closure]"
--     show (NBind _ x (PVar _ c info ty) _)
--       = withPiInfo info ("pat " ++ showCount c ++ show x ++ " : " ++ show ty) ++
--         " => [closure]"
--     show (NBind _ x (PLet _ c val ty) _)
--       = "plet " ++ showCount c ++ show x ++ " : " ++ show ty ++
--         " = " ++ show val ++ " in [closure]"
--     show (NBind _ x (PVTy _ c ty) _)
--       = "pty " ++ showCount c ++ show x ++ " : " ++ show ty ++
--         " => [closure]"
--     show (NApp _ hd args) = show hd ++ " [" ++ show (length args) ++ " closures " ++ showClosureSnocList (map @{Compose} snd args) ++ "]"
--     show (NDCon _ n _ _ args) = show n ++ " %DCon [" ++ show (length args) ++ " closures " ++ showClosureSnocList (map @{Compose} snd args) ++ "]"
--     show (NTCon _ n _ _ args) = show n ++ " %TCon [" ++ show (length args) ++ " closures " ++ showClosureSnocList (map @{Compose} snd args) ++ "]"
--     show (NAs _ _ n tm) = show n ++ "@" ++ show tm
--     show (NCase {}) = "Case"
--     show (NDelayed _ _ tm) = "%Delayed " ++ show tm
--     show (NDelay _ _ _ _) = "%Delay [closure]"
--     show (NForce _ _ tm args) = "%Force " ++ show tm ++ " [" ++ show (length args) ++ " closures " ++ showClosureSnocList (map @{Compose} snd args) ++ "]"
--     show (NPrimVal _ c) = show c
--     show (NPrimOp _ f args) = "%PrimOp " ++ show f ++ " " ++ show (length args)
--     show (NErased _ _) = "[__]"
--     show (NUnmatched _ str) = "Unmatched: " ++ show str
--     show (NType _ _) = "Type"
