/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.elaborator.alias
import init.lean.elaborator.basic
import init.lean.elaborator.preterm

namespace Lean
namespace Elab

partial def elabTermAux : Syntax Expr → Option Expr → Bool → Elab (Syntax Expr)
| stx, expectedType, expanding => stx.ifNode
  (fun n => do
    s ← get;
    let tables := termElabAttribute.ext.getState s.env;
    let k      := n.getKind;
    match tables.find k with
    | some elab => do
      newStx ← elab n expectedType;
      match newStx with
      | Syntax.other _ => pure newStx
      | _              => elabTermAux newStx expectedType expanding
    | none      => do
      -- recursively expand syntax
      let k := n.getKind;
      args ← n.getArgs.mmap $ fun arg => elabTermAux arg none true;
      let newStx := Syntax.node k args;
      -- if it was already expanding just return new node, otherwise invoke old elaborator
      if expanding then
        pure newStx
      else
        Syntax.other <$> oldElaborate newStx expectedType)
  (fun _ =>
    if expanding then pure stx
    else match stx with
    | Syntax.other e => pure stx
    | _              => throw "term elaborator failed, unexpected syntax")

def elabTerm (stx : Syntax Expr) (expectedType : Option Expr := none) : Elab (Syntax Expr) :=
elabTermAux stx expectedType false

open Lean.Parser

@[builtinTermElab «list»] def elabList : TermElab :=
fun stx _ => do
  let openBkt  := stx.getArg 0;
  let args     := stx.getArg 1;
  let closeBkt := stx.getArg 2;
  let consId   := openBkt.mkIdent `List.cons;
  let nilId    := closeBkt.mkIdent `List.nil;
  pure $ args.foldSepArgs (fun arg r => mkAppStx consId [arg, r]) nilId

@[builtinTermElab arrow] def elabArrow : TermElab :=
fun stx _ => do
  id ← mkFreshName;
  runIO (IO.println stx.val);
  pure $ Syntax.other $ Expr.sort (Level.zero)

end Elab
end Lean
