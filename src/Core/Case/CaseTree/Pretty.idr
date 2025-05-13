module Core.Case.CaseTree.Pretty

import Core.Context
import Core.Env
import Core.TT
import Core.Case.CaseTree
import Idris.Syntax
import Idris.Pretty
import Idris.Resugar

import Data.String
import Libraries.Data.String.Extra
import Libraries.Text.PrettyPrint.Prettyprinter

namespace Raw

  export
  prettyTree : {vars : _} -> CaseTree vars -> Doc IdrisSyntax
  prettyAlt : {vars : _} -> CaseAlt vars -> Doc IdrisSyntax
  prettyScope : {vars : _} -> CaseScope vars -> Doc IdrisSyntax

  prettyTree (Case {name} idx prf ty alts)
      = let ann = case ty of
                    Erased _ _ => ""
                    _ => space <+> keyword ":" <++> byShow ty
        in case_ <++> annotate Bound (pretty0 name) <+> ann <++> of_
         <+> nest 2 (hardline
         <+> vsep (assert_total (map prettyAlt alts)))
  prettyTree (STerm i tm) = byShow tm
  prettyTree (TUnmatched msg) = "Error:" <++> pretty0 msg
  prettyTree Impossible = "Impossible"

  prettyScope (RHS tm) = fatArrow <++> byShow tm
  prettyScope (Arg c x sc) = annotate Bound (pretty0 x) <++> prettyScope sc

  prettyAlt (ConCase n tag sc)
      = annotate (DCon (Just n)) (pretty0 n) <++> prettyScope sc
  prettyAlt (DelayCase _ arg sc) =
        keyword "Delay" <++> pretty0 arg
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt (ConstCase c sc) =
        pretty c
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt (DefaultCase sc) =
        keyword "_"
        <++> fatArrow
        <+> let sc = prettyTree sc in
            Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))

namespace Resugared

  prettyName : {auto c : Ref Ctxt Defs} ->
               Name -> Core (Doc IdrisSyntax)
  prettyName nm
    = pure $ ifThenElse (fullNamespace !(getPPrint))
               (pretty0 nm)
               (cast $ prettyOp True $ dropNS nm)

  export
  prettyTree : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> CaseTree vars -> Core (Doc IdrisSyntax)
  prettyAlt : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> CaseAlt vars -> Core (Doc IdrisSyntax)
  prettyScope : {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    Env Term vars -> CaseScope vars -> Core (Doc IdrisSyntax)

  prettyTree env (Case {name} idx prf ty alts) = do
    ann <- case ty of
             Erased _ _ => pure ""
             _ => do ty <- resugar env ty
                     pure (space <+> keyword ":" <++> pretty ty)
    alts <- assert_total (traverse (prettyAlt env) alts)
    pure $ case_ <++> pretty0 name <+> ann <++> of_
       <+> nest 2 (hardline <+> vsep alts)
  prettyTree env (STerm i tm) = pretty <$> resugar env tm
  prettyTree env (TUnmatched msg) = pure ("Error:" <++> pretty0 msg)
  prettyTree env Impossible = pure "Impossible"

  prettyScope env (RHS tm) = do
      tm <- prettyTree env tm
      pure $ fatArrow <++> tm
  prettyScope env (Arg c x sc) = do
      sc <- prettyScope (env :< PVar emptyFC top Explicit (Erased emptyFC Placeholder)) sc
      pure $ annotate Bound (pretty0 x) <++> sc

  prettyAlt env (ConCase n tag sc) = do
    sc <- prettyScope env sc
    pure $ annotate (DCon (Just n)) (pretty0 n) <++> sc
  prettyAlt env (DelayCase _ arg sc) = do
    sc <- prettyTree (mkEnvOnto emptyFC [_,_] env) sc
    pure $ keyword "Delay" <++> pretty0 arg
        <++> fatArrow
        <+> Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt env (ConstCase c sc) = do
    sc <- prettyTree env sc
    pure $ pretty c
        <++> fatArrow
        <+> Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
  prettyAlt env (DefaultCase sc) = do
    sc <- prettyTree env sc
    pure $ keyword "_"
        <++> fatArrow
        <+> Union (spaces 1 <+> sc) (nest 2 (hardline <+> sc))
