module Deriving.Common

import Data.SnocList
import Data.Maybe
import Language.Reflection

%default total

------------------------------------------------------------------------------
-- Being free of a variable

||| IsFreeOf is parametrised by
||| @ x  the name of the type variable that the functorial action will change
||| @ ty the type that does not contain any mention of x
export
data IsFreeOf : (x : Name) -> (ty : TTImp) -> Type where
  ||| For now we do not bother keeping precise track of the proof that a type
  ||| is free of x
  TrustMeFO : IsFreeOf a x

||| We may need to manufacture proofs and so we provide the `assert` escape hatch.
export %unsafe
assert_IsFreeOf : IsFreeOf x ty
assert_IsFreeOf = TrustMeFO

||| Testing function deciding whether the given term is free of a particular
||| variable.
export
isFreeOf : (x : Name) -> (ty : TTImp) -> Maybe (IsFreeOf x ty)
isFreeOf x ty
  = do isOk <- flip mapMTTImp ty $ \case
         t@(IVar _ v) => t <$ guard (v /= x)
         t => pure t
       pure TrustMeFO

------------------------------------------------------------------------------
-- Being a (data) type

mutual
  public export
  data TypeParameter
    = MkTPLocal Name
    | MkTPPrim Constant
    | MkTPType IsType
    | MkTPIType

  public export
  record IsType where
    constructor MkIsType
    typeConstructor  : Name
    typeParameters   : List (Argument TypeParameter, Nat)
    dataConstructors : List (Name, TTImp)

Show a => Show (Argument a) where
  show (Arg fc a) = "Arg _ (\{show a})"
  show (NamedArg fc nm a) = "NamedArg _ (\{show nm}) (\{show a})"
  show (AutoArg fc a) = "AutoArg _ (\{show a})"

mutual
  export
  Show TypeParameter where
    show (MkTPLocal a) = "MkTPLocal \{show a}"
    show (MkTPPrim c) = "MkTPPrim \{show c}"
    show (MkTPType i) = "MkTPType \{assert_total $ show i}"
    show MkTPIType = "MkTPIType"

  export
  Show IsType where
    show (MkIsType ctor params dcons) = "MkIsType (\{show ctor}) (\{show params}) (\{show dcons})"

wording : NameType -> String
wording Bound = "a bound variable"
wording Func = "a function name"
wording (DataCon tag arity) = "a data constructor"
wording (TyCon tag arity) = "a type constructor"

checkAccessToDefinition : Elaboration m => (given, candidate : TT.Name) -> m Bool
checkAccessToDefinition g c = do
  let False = isParentOf (getNS g) (getNS c)
    | _ => do
      logMsg "derive.common.checkAccessToDefinition" 100 "\{show g} is parent of \{show c}"
      pure True

  case !(getVis g) of
    [(_, Public)] => pure True
    other => do
      logMsg "derive.common.checkAccessToDefinition" 100 "\{show g} has not a public visibility: \{show other}"
      pure False
  where
    getNS : TT.Name -> TT.Namespace
    getNS (NS ns nm) = ns
    getNS nm = TT.MkNS []

    isParentOf : (given, candidate : TT.Namespace) -> Bool
    isParentOf (MkNS ms) (MkNS ns)
      = List.isSuffixOf ms ns

normaliseTypeFunction : Elaboration m => FC -> Name -> m Name
normaliseTypeFunction fc typeFunName = do
  [(_, typeFun)] <- getType typeFunName
    | _ => do
      logMsg "derive.common.isTypeCon" 100 "failAt: \{show typeFunName} is ambiguous"
      failAt fc "\{show typeFunName} is ambiguous"

  Just typedFun <- catch $ check {expected = Type} typeFun
    | _ => do
      logMsg "derive.common.normaliseTypeFunction" 100 "failAt: \{show typeFunName} (\{show typeFun}) is not a Type declaration"
      failAt fc "\{show typeFunName} is not a Type declaration"

  quotedTypedFun <- quote typedFun
  logMsg "derive.common.normaliseTypeFunction" 100 "\{show typeFunName} has detected type: \{show quotedTypedFun}"

  Just checkedTy <- catch $ check {expected = typedFun} $ IVar fc typeFunName
    | _ => failAt fc "\{show typeFunName} has a different type than checked: \{show quotedTypedFun}"

  normalisedTy <- quote checkedTy
  logMsg "derive.common.isTypeCon" 100 "\{show typeFunName} (\{show typeFun}) is normalised to: \{show normalisedTy}"

  let tyq@(_, Just typeName) = getHeadName normalisedTy
    | (broken, _) => do
      logMsg "derive.common.isTypeCon" 100 "failAt: Failed to extract a type name from normalised form \{show typeFunName} (\{show normalisedTy}) at \{show broken}"
      failAt fc "Failed to extract a type name from normalised form \{show typeFunName} (\{show normalisedTy}) at \{show broken}"

  logMsg "derive.common.normaliseTypeFunction" 100 "\{show typeFunName} is normalised to a function name \{show typeName}"

  [(_, MkNameInfo (TyCon _ _))] <- getInfo typeName
    | _ => failAt fc "\{show typeName} is not a type constructor name"

  pure typeName
  where
    getHeadName : TTImp -> (TTImp, Maybe Name)
    getHeadName t@(IVar _ n) = (t, pure n)
    getHeadName (IApp _ n _) = getHeadName n
    getHeadName (INamedApp _ n _ _) = getHeadName n
    getHeadName (IAutoApp _ n _) = getHeadName n
    getHeadName (IWithApp _ n _) = getHeadName n
    getHeadName (IPi _ _ _ _ _ retTy) = getHeadName retTy
    getHeadName (ILam _ _ _ _ _ retTy) = getHeadName retTy
    getHeadName t = (t, Nothing)

isTypeCon : Elaboration m => FC -> Name -> m (List (Name, TTImp))
isTypeCon fc ty = do
    [(_, MkNameInfo (TyCon _ _))] <- getInfo ty
      | [(fullName, MkNameInfo Func)] => analyzeFunctionName fullName
      | [] => do
        logMsg "derive.common.isTypeCon" 100 "failAt: \{show ty} out of scope"
        failAt fc "\{show ty} out of scope"
      | [(_, MkNameInfo nt)] => do
        logMsg "derive.common.isTypeCon" 100 "failAt: \{show ty} is \{wording nt} rather than a type constructor"
        failAt fc "\{show ty} is \{wording nt} rather than a type constructor"
      | _ => do
        logMsg "derive.common.isTypeCon" 100 "failAt: \{show ty} is ambiguous"
        failAt fc "\{show ty} is ambiguous"

    getDCons ty
  where
    getDCons : Name -> m (List (Name, TTImp))
    getDCons ty = do
      logMsg "derive.common.isTypeCon" 100 "Attempt to getCons over \{show ty}"
      cs <- getCons ty
      logMsg "derive.common.isTypeCon" 100 "getCons success for \{show ty}: \{show cs}"
      for cs $ \ n => do
        [(_, ty')] <- getType n
          | _ => do
            logMsg "derive.common.isTypeCon" 100 "failAt: \{show ty} is ambiguous"
            failAt fc "\{show n} is ambiguous"
        pure (n, ty')

    analyzeFunctionName : Name -> m (List (Name, TTImp))
    analyzeFunctionName fullName = do
      currentFn <- getCurrentFn
      let (Just currentName) = first currentFn
        | _ => failAt fc "Deriving requires a function declaration, not a top level"

      when (not !(checkAccessToDefinition fullName currentName)) $
        failAt fc "Make sure \{show fullName} has public export visibility"

      normalisedTypeName <- normaliseTypeFunction fc fullName

      when (not !(checkAccessToDefinition normalisedTypeName fullName)) $
        failAt fc "Make sure \{show normalisedTypeName} has public export visibility"

      getDCons normalisedTypeName
      where
        first : SnocList Name -> Maybe Name
        first [<]       = Nothing
        first [<x]      = Just x
        first (xs :< _) = first xs

export
isType : Elaboration m => TTImp -> m IsType
isType t = do
  logMsg "derive.common.isType" 100 "Attempt to run over: \{show t}"
  ist <- go Z [] t
  logMsg "derive.common.isType" 100 "Result received for \{show t}: \{show ist}"
  pure ist
where
  go : Nat -> List (Argument TypeParameter, Nat) -> TTImp -> m IsType
  go idx acc (IVar fc n) = MkIsType n (map (map (minus idx . S)) acc) <$> isTypeCon fc n
  go idx acc (IApp fc t arg) = case arg of
    IType fc => go (S idx) ((Arg fc $ MkTPIType, idx) :: acc) t
    IPrimVal fc c => go (S idx) ((Arg fc $ MkTPPrim c, idx) :: acc) t
    -- Unqualified: that's a local variable
    IVar fc nm@(UN (Basic _)) => go (S idx) ((Arg fc $ MkTPLocal nm, idx) :: acc) t
    _ => go (S idx) ((Arg fc $ MkTPType !(isType arg), idx) :: acc) t
  go idx acc (INamedApp fc t nm arg) = case arg of
    IType fc => go (S idx) ((NamedArg fc nm $ MkTPIType, idx) :: acc) t
    IPrimVal fc c => go (S idx) ((NamedArg fc nm $ MkTPPrim c, idx) :: acc) t
    -- Unqualified: that's a local variable
    IVar fc nm'@(UN (Basic _)) => go (S idx) ((NamedArg fc nm $ MkTPLocal nm', idx) :: acc) t
    _ => go (S idx) ((NamedArg fc nm $ MkTPType !(isType arg), idx) :: acc) t
  go idx acc (IAutoApp fc t arg) = case arg of
    IType fc => go (S idx) ((AutoArg fc $ MkTPIType, idx) :: acc) t
    IPrimVal fc c => go (S idx) ((AutoArg fc $ MkTPPrim c, idx) :: acc) t
    -- Unqualified: that's a local variable
    IVar fc nm'@(UN (Basic _)) => go (S idx) ((AutoArg fc $ MkTPLocal nm', idx) :: acc) t
    _ => go (S idx) ((AutoArg fc $ MkTPType !(isType arg), idx) :: acc) t
  go idx acc t = failAt (getFC t) "Expected a type constructor, got: \{show t}"

------------------------------------------------------------------------------
-- Being a (data) constructor with a parameter
-- TODO: generalise?

public export
record ConstructorView where
  constructor MkConstructorView
  params      : SnocList (Name, Nat)
  conArgTypes : List (Count, Argument TTImp)

export
constructorView : TTImp -> Maybe ConstructorView
constructorView (IPi fc rig pinfo x a b) = do
  let Just arg = fromPiInfo fc pinfo x a
    | Nothing => constructorView b -- this better be a boring argument...
  let True = rig /= M1
    | False => constructorView b -- this better be another boring argument...
  { conArgTypes $= ((rig, arg) ::) } <$> constructorView b
constructorView f = do
  MkAppView _ ts _ <- appView f
  let range = [<] <>< [0..minus (length ts) 1]
  let ps = flip mapMaybe (zip ts range) $ \ t => the (Maybe (Name, Nat)) $ case t of
             (Arg _ (IVar _ nm), n) => Just (nm, n)
             _ => Nothing
  pure (MkConstructorView ps [])

------------------------------------------------------------------------------
-- Satisfying an interface
--
-- In order to derive Functor for `data Tree a = Node (List (Tree a))`, we need
-- to make sure that `Functor List` already exists. This is done using the following
-- convenience functions.

export
withParams : FC -> (Nat -> Maybe TTImp) -> List (Argument TypeParameter, Nat) -> TTImp -> TTImp
withParams fc params nms t = go nms where

  addConstraint : Maybe TTImp -> Name -> TTImp -> TTImp
  addConstraint Nothing _ = id
  addConstraint (Just cst) nm =
     let ty = IApp fc cst (IVar fc nm) in
     IPi fc MW AutoImplicit Nothing ty

  go : List (Argument TypeParameter, Nat) -> TTImp
  go [] = t
  go ((arg, pos) :: nms) with (unArg arg)
    go ((arg, pos) :: nms) | MkTPLocal nm =
      IPi fc M0 ImplicitArg (Just nm) (Implicit fc True)
      $ addConstraint (params pos) nm
      $ go nms
    go ((arg, pos) :: nms) | MkTPPrim _ = go nms
    go ((arg, pos) :: nms) | MkTPType _ = go nms
    go ((arg, pos) :: nms) | MkTPIType  = go nms

||| Type of proofs that something has a given type
export
data HasType : (nm : Name) -> (ty : TTImp) -> Type where
  TrustMeHT : HasType nm ty

export
hasType : Elaboration m => (nm : Name) ->
          m (Maybe (ty : TTImp ** HasType nm ty))
hasType nm = catch $ do
  [(_, ty)] <- getType nm
    | _ => fail "Ambiguous name"
  pure (ty ** TrustMeHT)

||| Type of proofs that a type is inhabited
export
data IsProvable : (ty : TTImp) -> Type where
  TrustMeIP : IsProvable ty

export
isProvable : Elaboration m => (ty : TTImp) ->
             m (Maybe (IsProvable ty))
isProvable ty = catch $ do
  ty <- check {expected = Type} ty
  ignore $ check {expected = ty} `(%search)
  pure TrustMeIP

||| Type of proofs that a type satisfies a constraint.
||| Internally it's vacuous. We don't export the constructor so
||| that users cannot manufacture buggy proofs.
export
data HasImplementation : (intf : a -> Type) -> TTImp -> Type where
  TrustMeHI : HasImplementation intf t

||| We may need to manufacture proofs and so we provide the `assert` escape hatch.
export %unsafe
assert_hasImplementation : HasImplementation intf t
assert_hasImplementation = TrustMeHI

||| Given
||| @ intf an interface (e.g. `Functor`, or `Bifunctor`)
||| @ t    a term corresponding to a (possibly partially applied) type constructor
||| check whether Idris2 can find a proof that t satisfies the interface.
export
hasImplementation : Elaboration m => (intf : a -> Type) -> (t : TTImp) ->
                    m (Maybe (HasImplementation intf t))
hasImplementation c t = do
  Just prf <- catch $ isType t
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "\{show t} is derived as not a Type"
  Just intf <- catch $ quote c
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "Could not quote constraint"
  Just ty <- catch $ check {expected = Type} $
               withParams emptyFC (const Nothing) prf.typeParameters `(~(intf) ~(t))
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "\{show (`(~(intf) ~(t)))} is checked as not a Type"

  Just _ <- catch $ check {expected = ty} `(%search)
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "Could not find an implementation of \{show (`(~(intf) ~(t)))}"
  pure (Just TrustMeHI)

------------------------------------------------------------------------------
-- Utils

||| Optionally eta-expand if there is no argument available
export
optionallyEta : FC -> Maybe TTImp -> (TTImp -> TTImp) -> TTImp
optionallyEta fc (Just t) f = f t
optionallyEta fc Nothing f =
  let tnm = UN $ Basic "t" in
  ILam fc MW ExplicitArg (Just tnm) (Implicit fc False) $
  f (IVar fc tnm)

||| We often apply multiple arguments, this makes things simpler
export
apply : FC -> TTImp -> List TTImp -> TTImp
apply fc t ts = apply t (map (Arg fc) ts)

||| Use unqualified names (useful for more compact printing)
export
cleanup : TTImp -> TTImp
cleanup = \case
  IVar fc n => IVar fc (dropNS n)
  t => t

||| Create fresh names
export
freshName : List TypeParameter -> String -> String
freshName ns a = assert_total $ go (basicNames $ concatMap typeParameterNames ns) Nothing where
  typeParameterNames : TypeParameter -> List Name
  typeParameterNames (MkTPLocal a) = pure a
  typeParameterNames (MkTPPrim c) = []
  typeParameterNames (MkTPType (MkIsType n tp _)) = assert_total
    $ [n] ++ concatMap (typeParameterNames . unArg . fst) tp
  typeParameterNames MkTPIType = []

  basicNames : List Name -> List String
  basicNames = mapMaybe $ \ nm => case dropNS nm of
    UN (Basic str) => Just str
    _ => Nothing

  covering
  go : List String -> Maybe Nat -> String
  go ns mi =
    let nm = a ++ maybe "" show mi in
    ifThenElse (nm `elem` ns) (go ns (Just $ maybe 0 S mi)) nm
