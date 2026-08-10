import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

open Lean Meta Elab Command Term
#eval show CommandElabM Unit from liftTermElabM do
  let target ← elabTerm (← `(∀ n : ℕ, n > 0 → a n > 0)) none
  let target ← instantiateMVars target
  let env ← getEnv
  let mut c := 0
  for (name, ci) in env.constants.toList do
    try
      if (← isDefEq ci.type target) then
        logInfo m!"MATCH {name}"
        c := c + 1
    catch _ => pure ()
  logInfo m!"done {c}"
