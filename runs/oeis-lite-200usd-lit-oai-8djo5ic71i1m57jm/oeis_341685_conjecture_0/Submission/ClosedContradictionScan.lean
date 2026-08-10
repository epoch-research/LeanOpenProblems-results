import FormalConjectures.Util.ProblemImports
open Lean Meta

unsafe def allowedArr (axs : Array Name) : Bool :=
  axs.all fun n => n == `propext || n == `Classical.choice || n == `Quot.sound

unsafe def noLooseBVars (e : Expr) : Bool := !e.hasLooseBVars

#eval show MetaM Unit from do
  let env ← getEnv
  let targets ← [
    mkConst ``False,
    (← elabType (← `(0 = (1 : ℕ)))),
    (← elabType (← `(1 = (0 : ℕ)))),
    (← elabType (← `((0 : ℤ) = 1))),
    (← elabType (← `((0 : ℚ) = 1))),
    (← elabType (← `(Subsingleton ℕ))),
    (← elabType (← `(Subsingleton ℚ))),
    (← elabType (← `(Finite ℕ))),
    (← elabType (← `(Fintype ℕ))),
    (← elabType (← `(IsEmpty ℕ))),
    (← elabType (← `(Nonempty False)))
  ].toArray
  let mut count := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let axs ← Lean.collectAxioms n
      if allowedArr axs then
        let ty ← instantiateMVars ci.type
        for t in targets do
          if ← isDefEq ty t then
            logInfo m!"MATCH {n} : {← ppExpr ty} | axioms {axs}"
            count := count + 1
    | _ => pure ()
  logInfo m!"count {count}"
