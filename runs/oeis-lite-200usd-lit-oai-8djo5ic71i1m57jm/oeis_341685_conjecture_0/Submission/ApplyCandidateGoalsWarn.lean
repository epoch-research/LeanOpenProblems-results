import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

open Lean Meta Elab Command Term

set_option maxHeartbeats 0

def allowedAxioms : NameSet := (NameSet.empty.insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def onlyAllowed (xs : Array Name) : Bool := xs.all (fun n => allowedAxioms.contains n)

elab "#apply_candidate_goals" : command => do
  let targetsStx : Array (TSyntax `term) := #[
    ← `(Module.Finite ℚ (Padic 3)),
    ← `(Algebra.IsAlgebraic ℚ (Padic 3)),
    ← `(IsAlgebraic ℚ xi_3),
    ← `(¬ IsAlgebraic ℚ xi_3)
  ]
  let mut targets := #[]
  for stx in targetsStx do targets := targets.push (← liftTermElabM <| Term.elabType stx)
  let env ← getEnv
  let mut printed : Nat := 0
  let interestingHead (ty : Expr) : Bool :=
    let cs := ty.getUsedConstants
    cs.contains ``Module.Finite || cs.contains ``FiniteDimensional || cs.contains ``IsAlgebraic ||
    cs.contains ``Algebra.IsAlgebraic || cs.contains ``LinearMap.det || cs.contains ``Algebra.norm ||
    cs.contains ``Polynomial.aeval || cs.contains ``Padic
  for (n, ci) in env.constants.toList do
    if printed >= 120 then break
    if n.isInternal then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      if !interestingHead ci.type then continue
      let axs ← Lean.collectAxioms n
      if !onlyAllowed axs then continue
      for tgt in targets do
        try
          let (ok, ppgoals) ← liftTermElabM <| do
            let mvar ← mkFreshExprSyntheticOpaqueMVar tgt
            let c ← mkConstWithFreshMVarLevels n
            let gs ← Expr.mvarId! mvar |>.apply c
            if gs.length <= 5 then
              let mut ppgoals : Array MessageData := #[]
              for g in gs do
                let t ← instantiateMVars (← g.getType)
                ppgoals := ppgoals.push (← ppExpr t)
              return (true, ppgoals)
            else
              return (false, #[])
          if ok then
            let pp ← liftTermElabM <| ppExpr ci.type
            logWarning m!"CAND {n} : {pp}\n  subgoals: {ppgoals}"
            printed := printed + 1
        catch _ => pure ()
    | _ => pure ()
  logWarning m!"printed {printed}"

#apply_candidate_goals
