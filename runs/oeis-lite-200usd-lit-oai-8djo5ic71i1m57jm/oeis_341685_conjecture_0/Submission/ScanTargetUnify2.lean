import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 1000000
open Lean Meta Elab Command
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_scan : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

unsafe def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

elab "#scan_target_unify2" : command => unsafe do
  liftTermElabM do
    let target ← Lean.Elab.Term.elabType (← `(¬ IsAlgebraic ℚ xi_3_scan))
    let alg ← Lean.Elab.Term.elabType (← `(IsAlgebraic ℚ xi_3_scan))
    let falseExpr ← Lean.Elab.Term.elabType (← `(False))
    let env ← getEnv
    for (n, ci) in env.constants.toList do
      if !n.isInternal then
        let axs ← Lean.collectAxioms n
        if axs.all (fun a => allowedAxioms.contains a) then
          let ty ← instantiateMVars ci.type
          forallTelescopeReducing ty fun xs body => do
            for (label, tgt) in #[("neg", target), ("alg", alg), ("false", falseExpr)] do
              try
                if (← isDefEq body tgt) then
                  IO.println s!"CAND {label} {n} : {← ppExpr ci.type}"
              catch _ => pure ()

#scan_target_unify2
