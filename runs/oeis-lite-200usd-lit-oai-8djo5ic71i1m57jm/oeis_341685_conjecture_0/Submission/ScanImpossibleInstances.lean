import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from Command.liftTermElabM do
  let tests := #[
    (← `(Fact False)), (← `(Fact (0 = 1))), (← `(Fact ((0:ℕ) ≠ 0))), (← `(NeZero (0:ℕ))),
    (← `(Subsingleton ℕ)), (← `(Unique ℕ)), (← `(IsEmpty ℕ)), (← `(Finite ℕ)),
    (← `(Fintype ℚ)), (← `(Finite ℚ)), (← `(Subsingleton ℚ)), (← `(CharP ℚ 1)),
    (← `(Fact (Nat.Prime 1))), (← `(Fact (Nat.Prime 0))), (← `(Fact (Nat.Prime 4)))]
  for stx in tests do
    try
      let ty ← Lean.Elab.Term.elabType stx
      let inst ← synthInstance ty
      logInfo m!"SYNTH {stx} := {inst}"
    catch _ => pure ()
