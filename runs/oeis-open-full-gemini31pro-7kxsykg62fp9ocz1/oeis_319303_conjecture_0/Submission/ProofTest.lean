import Mathlib
import Submission.Spec2

open Lean Elab Tactic in
elab "print_goal" : tactic => do
  let goal ← getMainGoal
  let goalType ← Meta.inferType (← goal.getType)
  logInfo m!"{goal}"

