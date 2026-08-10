import FormalConjectures.Util.ProblemImports

open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

open Lean Meta Elab Command
open Lean.Elab Term

elab "#target_search" : command => do
  let target ← liftTermElabM <| Term.elabType (← `(¬ IsAlgebraic ℚ (xi_3)))
  let dispt ← liftTermElabM <| Term.elabType (← `(¬ (¬ IsAlgebraic ℚ (xi_3))))
  let algt ← liftTermElabM <| Term.elabType (← `(IsAlgebraic ℚ (xi_3)))
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 50 then break
    if n.isInternal then continue
    let ty ← liftTermElabM <| instantiateMVars ci.type
    if ty == target || ty == dispt || ty == algt then
      let pp ← liftTermElabM <| Meta.ppExpr ty
      logInfo m!"EXACT {n} : {pp}"
      printed := printed + 1
  logInfo m!"done {printed}"

#target_search
