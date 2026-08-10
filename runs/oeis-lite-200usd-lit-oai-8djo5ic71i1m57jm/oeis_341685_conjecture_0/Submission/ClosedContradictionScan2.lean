import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Term

unsafe def allowedArr (axs : Array Name) : Bool :=
  axs.all fun n => n == `propext || n == `Classical.choice || n == `Quot.sound

unsafe def scanClosedContradictions : TermElabM Unit := do
  let targetsList : List Syntax ← pure [
    (← `(False)),
    (← `((0 : ℕ) = 1)),
    (← `((1 : ℕ) = 0)),
    (← `((0 : ℤ) = 1)),
    (← `((0 : ℚ) = 1)),
    (← `((True : Prop) = False)),
    (← `((False : Prop) = True)),
    (← `(Subsingleton ℕ)),
    (← `(Subsingleton ℚ)),
    (← `(Finite ℕ)),
    (← `(Fintype ℕ)),
    (← `(IsEmpty ℕ)),
    (← `(Nonempty False)),
    (← `(Inhabited False)),
    (← `(Unique ℕ)),
    (← `(∀ n : ℕ, n = 0)),
    (← `(∀ q : ℚ, q = 0))
  ]
  let mut targets : Array Expr := #[]
  for stx in targetsList do
    targets := targets.push (← elabType stx)
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ | .axiomInfo _ =>
      let axs ← Lean.collectAxioms n
      if allowedArr axs then
        let ty ← instantiateMVars ci.type
        if !ty.hasLooseBVars then
          for t in targets do
            try
              if ← isDefEq ty t then
                logInfo m!"MATCH {n} : {← ppExpr ty} | axioms {axs}"
                count := count + 1
            catch _ => pure ()
    | _ => pure ()
  logInfo m!"count {count}"

#eval scanClosedContradictions
