import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_scan : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#eval show CommandElabM Unit from do
  liftTermElabM do
    let target ← Lean.Elab.Term.elabType (← `(¬ IsAlgebraic ℚ xi_3_scan))
    let alg ← Lean.Elab.Term.elabType (← `(IsAlgebraic ℚ xi_3_scan))
    let falseExpr ← Lean.Elab.Term.elabType (← `(False))
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      let ty ← instantiateMVars ci.type
      forallTelescopeReducing ty fun xs body => do
        for (label, tgt) in #[("neg", target), ("alg", alg), ("false", falseExpr)] do
          try
            if (← isDefEq body tgt) then
              let fmt ← ppExpr ci.type
              logInfo m!"CAND {label} {n} : {fmt}"
          catch _ => pure ()
