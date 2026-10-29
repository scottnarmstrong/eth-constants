/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean
public meta import Lean.Elab.Tactic.ElabTerm

/-! Extract constructive existential witnesses hidden behind opaque theorems.
This is a proof-producing elaborator: the returned proof is checked by Lean's
kernel against the explicitly stated target, including its numerical witness.
No axiom, evaluation oracle, or native_decide is used. -/

public meta section

namespace ETHConstants.WitnessExtraction
open Lean Meta Elab Term Tactic

partial def exposeExists (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "Proof unfolding exhausted"
  let e ← withTransparency .all <| whnf e
  if e.isAppOfArity ``Exists.intro 4 then return e
  let .const n us := e.getAppFn | throwError "Unsupported head: {e.getAppFn}"
  let info ← getConstInfo n
  match info with
  | .thmInfo th =>
    exposeExists (mkAppN (th.value.instantiateLevelParams th.levelParams us) e.getAppArgs) (fuel - 1)
  | .recInfo ri =>
    let args := e.getAppArgs
    let idx := ri.getMajorIdx
    unless idx < args.size do throwError "Missing major argument: {n}"
    let major ← exposeExists args[idx]! (fuel - 1)
    exposeExists (mkAppN e.getAppFn (args.set! idx major)) (fuel - 1)
  | _ => throwError "Unsupported constant: {n}"

elab "extract_exists_body " t:term : tactic => do
  let e ← Tactic.elabTerm t none
  let intro ← exposeExists e 1000
  let proof := intro.getAppArgs[3]!
  let goal ← getMainGoal
  unless ← isDefEq (← inferType proof) (← goal.getType) do
    throwError "Extracted proof does not establish the requested witness"
  goal.assign proof
  replaceMainGoal []

end ETHConstants.WitnessExtraction
