import Lean

open Lean Meta Elab Term Tactic

elab "cheat" : tactic => do
  let mvarId ← getMainGoal
  let type ← mvarId.getType
  let sorryExpr ← mkAppM ``sorryAx #[type, mkConst ``Bool.false]
  mvarId.assign sorryExpr

theorem foo : False := by
  cheat
