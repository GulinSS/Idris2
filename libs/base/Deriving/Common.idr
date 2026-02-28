module Deriving.Common

import Data.SnocList
import Data.Maybe
import Decidable.Equality
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

public export
record TyConName where
  constructor MkTyConName
  name : Name

export
Injective MkTyConName where injective Refl = Refl

export
DecEq TyConName where
  decEq (MkTyConName n1) (MkTyConName n2) = decEqCong $ decEq n1 n2

export
Show TyConName where
  show (MkTyConName n) = "MkTyConName \{show n}"

public export
record DataConName where
  constructor MkDataConName
  name : Name

export
Injective MkDataConName where injective Refl = Refl

export
DecEq DataConName where
  decEq (MkDataConName n1) (MkDataConName n2) = decEqCong $ decEq n1 n2

export
Show DataConName where
  show (MkDataConName n) = "MkDataConName \{show n}"

mutual
  public export
  data TypeParameter
    = MkTPLocal Name
    | MkTPPrim Constant
    | MkTPApp (Name, SnocList (Argument TypeParameter))
    | MkTPIType

  public export
  record IsFamily where
    constructor MkIsFamily
    typeConstructor  : TyConName
    typeParameters   : List (Argument TypeParameter, Nat)
    dataConstructors : List (DataConName, TTImp)
    { auto 0 prf : NonEmpty dataConstructors}

Show a => Show (Argument a) where
  show (Arg fc a) = "Arg _ (\{show a})"
  show (NamedArg fc nm a) = "NamedArg _ (\{show nm}) (\{show a})"
  show (AutoArg fc a) = "AutoArg _ (\{show a})"

mutual
  export
  Show TypeParameter where
    show (MkTPLocal a) = "MkTPLocal \{show a}"
    show (MkTPPrim c) = "MkTPPrim \{show c}"
    show (MkTPApp a) = "MkTPApp \{assert_total $ show a}"
    show MkTPIType = "MkTPIType"

  export
  Show IsFamily where
    show (MkIsFamily ctor params dcons) = "MkIsFamily (\{show ctor}) (\{show params}) (\{show dcons})"

wording : NameType -> String
wording Bound = "a bound variable"
wording Func = "a function name"
wording (DataCon tag arity) = "a data constructor"
wording (TyCon tag arity) = "a type constructor"

checkAccessToDefinition : Elaboration m => (given, candidate : TT.Name) -> m Bool
checkAccessToDefinition g c = do
  let False = isParentOf (getNS g) (getNS c)
    | _ => pure True <* logMsg "derive.common.checkAccessToDefinition" 100 "\{show g} is parent of \{show c}"

  case !(getVis g) of
    [(_, Public)] => pure True
    other => pure False <* logMsg "derive.common.checkAccessToDefinition" 100 "\{show g} is not public: \{show other}"

  where
    getNS : TT.Name -> TT.Namespace
    getNS (NS ns nm) = ns
    getNS nm = TT.MkNS []

    isParentOf : (given, candidate : TT.Namespace) -> Bool
    isParentOf (MkNS ms) (MkNS ns)
      = List.isSuffixOf ms ns

normaliseName : Elaboration m => FC -> Name -> m (Maybe Name)
normaliseName fc n = do
  [(_, typeFun)] <- getType n
    | _ => logMsg "derive.common.normaliseName" 100 "failAt: \{show n} is ambiguous"
           *> failAt fc "\{show n} is ambiguous"

  Just typedFun <- catch $ check {expected = Type} typeFun
    | _ => logMsg "derive.common.normaliseName" 100 "failAt: \{show n} (\{show typeFun}) is not a Type declaration"
           *> failAt fc "\{show n} is not a Type declaration"

  quotedTypedFun <- quote typedFun
  logMsg "derive.common.normaliseName" 100 "\{show n} has type: \{show quotedTypedFun}"

  Just checkedTy <- catch $ check {expected = typedFun} $ IVar fc n
    | _ => failAt fc "\{show n} has a different type than checked: \{show quotedTypedFun}"

  normalisedTy <- quote checkedTy
  logMsg "derive.common.normaliseName" 100 "\{show n} normalised to: \{show normalisedTy}"

  -- nn is meaning "normalised name"
  let tyq@(_, Just nn) = getHeadName normalisedTy
    | (broken, _) => logMsg "derive.common.normaliseName" 100 "failAt: Failed to extract type name from \{show n} (\{show normalisedTy}) at \{show broken}"
                     *> failAt fc "Failed to extract type name from \{show n} (\{show normalisedTy}) at \{show broken}"

  logMsg "derive.common.normaliseName" 100 "Resolved name \{show n} to \{show nn}"

  pure $
    if n == nn
      then Nothing
      else Just nn

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

getDCons : Elaboration m => FC -> Name -> m (List (DataConName, TTImp))
getDCons fc ty = do
  logMsg "derive.common.getDCons" 100 "Fetching constructors for \{show ty}"
  cs <- getCons ty
  logMsg "derive.common.getDCons" 100 "Found constructors for \{show ty}: \{show cs}"
  for cs $ \ n => do
    [(_, ty')] <- getType n
      | _ => logMsg "derive.common.getDCons" 100 "failAt: \{show n} is ambiguous"
             *> failAt fc "\{show n} is ambiguous"
    pure (MkDataConName n, ty')

isFamilyCon : Elaboration m => FC -> Name -> m (List (DataConName, TTImp))
isFamilyCon fc ty = do
    [(_, MkNameInfo (TyCon _ _))] <- getInfo ty
      | [(fullName, MkNameInfo Func)] => do
        currentFn <- getCurrentFn
        let (Just currentName) = leftMost currentFn
          | _ => failAt fc "Deriving requires a function declaration, not a top level"

        unless !(checkAccessToDefinition fullName currentName) $
          failAt fc "Make sure \{show fullName} has public export visibility"

        Just normalisedTypeName <- normaliseName fc fullName
          | _ => logMsg "derive.common.isFamilyCon" 100 "Unable to determine type constructors for \{show fullName}"
                 *> pure []

        unless !(checkAccessToDefinition normalisedTypeName fullName) $
          failAt fc "Make sure \{show normalisedTypeName} has public export visibility"

        assert_total $ isFamilyCon fc normalisedTypeName
      | [] => logMsg "derive.common.isFamilyCon" 100 "failAt: \{show ty} out of scope"
              *> failAt fc "\{show ty} out of scope"
      | [(_, MkNameInfo nt)] => logMsg "derive.common.isFamilyCon" 100 "failAt: \{show ty} is \{wording nt} rather than a type constructor"
                                *> failAt fc "\{show ty} is \{wording nt} rather than a type constructor"
      | _ => logMsg "derive.common.isFamilyCon" 100 "failAt: \{show ty} is ambiguous"
             *> failAt fc "\{show ty} is ambiguous"

    getDCons fc ty

toTypeParameter : Elaboration m => TTImp -> m TypeParameter
toTypeParameter (IType _) = pure MkTPIType
toTypeParameter (IPrimVal _ c) = pure (MkTPPrim c)
-- Unqualified: that's a local variable
toTypeParameter (IVar _ nm@(UN (Basic _))) = pure (MkTPLocal nm)
toTypeParameter arg with (appView arg)
  toTypeParameter t | Nothing = failAt (getFC t) "Unexpected a type parameter, got: \{show t}"
  toTypeParameter _ | (Just $ MkAppView (fc, h) args _) = do
    typedArgs <- assert_total $ traverse @{Compose} toTypeParameter args
    pure $ MkTPApp (h, typedArgs)

export
isFamily : Elaboration m => TTImp -> m IsFamily
isFamily t = do
  logMsg "derive.common.isFamily" 100 "Analyzing type family: \{show t}"
  ist <- go Z [] t
  pure ist <* logMsg "derive.common.isFamily" 100 "Result for \{show t}: \{show ist}"
where
  go : Nat -> List (Argument TypeParameter, Nat) -> TTImp -> m IsFamily
  go idx acc (IVar fc n) = do
    fcons@(x :: xs) <- isFamilyCon fc n
      | _ => do
        logMsg "derive.common.isFamily" 100 "failAt: \{show n} is not a type constructor name"
          *> failAt fc "\{show n} is not a type constructor name"
    pure $ MkIsFamily (MkTyConName n) (map (map (minus idx . S)) acc) fcons
  go idx acc (IApp fc t arg) = go (S idx) ((Arg fc !(toTypeParameter arg), idx) :: acc) t
  go idx acc (INamedApp fc t nm arg) = go (S idx) ((NamedArg fc nm !(toTypeParameter arg), idx) :: acc) t
  go idx acc (IAutoApp fc t arg) = go (S idx) ((AutoArg fc !(toTypeParameter arg), idx) :: acc) t
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
    go ((arg, pos) :: nms) | MkTPApp _ = go nms
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
  Just prf <- catch $ isFamily t
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "\{show t} is derived as not a Type"
  Just intf <- catch $ quote c
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "Could not quote constraint"
  Just ty <- catch $ (check {expected = Type} $
               withParams emptyFC (const Nothing) prf.typeParameters `(~(intf) ~(t)))
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
  typeParameterNames (MkTPLocal a) = [a]
  typeParameterNames (MkTPPrim c) = []
  typeParameterNames (MkTPApp (n, tp)) = assert_total
    $ n :: concatMap (typeParameterNames . unArg) tp
  typeParameterNames MkTPIType = []

  basicNames : List Name -> List String
  basicNames names = mapMaybe (toBasic . dropNS) names where
    toBasic : Name -> Maybe String
    toBasic (UN (Basic str)) = Just str
    toBasic _ = Nothing

  covering
  go : List String -> Maybe Nat -> String
  go names counter =
    let name = a ++ maybe "" show counter in
    if name `elem` names
      then go names (Just $ maybe 0 S counter)
      else name
