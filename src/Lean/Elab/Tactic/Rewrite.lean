/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic
open Meta

def rewriteTarget (stx : Syntax) (symm : Bool) (config : Rewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).rewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config := {}) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).rewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

def withRWRulesSeq (token : Syntax) (rwRulesSeqStx : Syntax) (x : (symm : Bool) → (term : Syntax) → TacticM Unit) : TacticM Unit := do
  let lbrak := rwRulesSeqStx[0]
  let rules := rwRulesSeqStx[1].getArgs
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
  let numRules := (rules.size + 1) / 2
  for i in [:numRules] do
    let rule := rules[i * 2]!
    -- IO.println s!"rule : {(← PrettyPrinter.formatTerm rule).pretty}"
    let sep  := rules.getD (i * 2 + 1) Syntax.missing
    -- show rule state up to (incl.) next `,`
    withTacticInfoContext (mkNullNode #[rule, sep]) do
      -- show errors on rule
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        let processId (id : Syntax) : TacticM Unit := do
          -- See if we can interpret `id` as a hypothesis first.
          if (← optional <| getFVarId id).isSome then
            x symm term
          else
            -- Try to get equation theorems for `id`.
            let declName ← try resolveGlobalConstNoOverload id catch _ => return (← x symm term)
            let some eqThms ← getEqnsFor? declName (nonRec := true) | x symm term
            let rec go : List Name →  TacticM Unit
              | [] => throwError "failed to rewrite using equation theorems for '{declName}'"
              | eqThm::eqThms => (x symm (mkIdentFrom id eqThm)) <|> go eqThms
            go eqThms.toList
            discard <| Term.addTermInfo id (← mkConstWithFreshMVarLevels declName) (lctx? := ← getLCtx)
        match term with
        | `($id:ident)  => processId id
        | `(@$id:ident) => processId id
        | _ => x symm term


declare_config_elab elabRewriteConfig Rewrite.Config

def traceExpandRw (stx : Syntax) : TacticM Unit := do
  let rules := stx[2][1].getArgs
  IO.println s!"rules: {(← PrettyPrinter.formatTerm stx[2]).pretty}"
  let numRules := (rules.size + 1) / 2
  -- let s ← saveState
  for i in [:numRules] do
    let rule := rules[i * 2]!
    let oneRuleStx : Syntax := stx.setArgs <| stx.getArgs.set! 2 <|
      stx[2].setArgs <| stx[2].getArgs.set! 1 <|
      stx[2][1].setArgs #[rule]

    -- rewrite -> rw
    -- let oneRuleStxRw := oneRuleStx.setArgs <| oneRuleStx.getArgs.set! 0 <| match stx[0] with
    -- | .missing => .missing
    -- | .node _ _ _ => .missing
    -- | .atom info val => if val == "rewrite" then .atom info "rewritw" else .missing
    -- | .ident _ _ _ _ => .missing

    -- if oneRuleStxRw.isMissing then
    --   throwError "ummm?"

    let startPos := stx.getPos?.getD (String.Pos.mk 0)
    let endPos := stx.getTailPos?.getD (String.Pos.mk 0)
    -- IO.println s!"heh? {(← PrettyPrinter.formatTerm oneRuleStx).pretty}"
    let ci : ContextInfo := {
      env := ← getEnv,
      fileMap := ← getFileMap,
      mctx := ← getMCtx,
      options := ← getOptions,
      currNamespace := ← getCurrNamespace,
      openDecls := ← getOpenDecls,
      ngen := ← getNGen
    }
    -- traceCanonicalInfo oneRuleStx startPos endPos ci "expandRw"
    withOptions (fun o => o.setBool `_doTracing false) <| evalTactic oneRuleStx
  -- s.restore


@[builtin_tactic Lean.Parser.Tactic.rewriteSeq] def evalRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  let rules := stx[2][1].getArgs
  if rules.size > 1 then Core.withoutCountHeartbeats <| do
    let eq := ← isEquivalentTactics
      (withRWRulesSeq stx[0] stx[2] fun symm term => do
        withLocation loc
          (rewriteLocalDecl term symm · cfg)
          (rewriteTarget term symm cfg)
          (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")
      )
      (traceExpandRw stx)
    if !eq then
      IO.println "yohooo!"

  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

end Lean.Elab.Tactic
