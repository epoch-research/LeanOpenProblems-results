import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Tactic

elab "apply_const" n:ident : tactic => do
  let name := n.getId
  liftMetaTactic fun g => do
    let e ← mkConstWithFreshMVarLevels name
    g.apply e

example : ¬ Powerfree 0 (0 : ℕ) := by
  apply_const not_powerfree_zero

example : False := by
  apply_const not_powerfree_zero
  all_goals first | infer_instance | simp | norm_num | omega | aesop
