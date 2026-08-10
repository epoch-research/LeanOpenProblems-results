import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#check collectAxioms
#eval show CommandElabM Unit from do
  let ax ← collectAxioms ``Nat.not_prime_zero
  logInfo m!"{ax.toList}"
