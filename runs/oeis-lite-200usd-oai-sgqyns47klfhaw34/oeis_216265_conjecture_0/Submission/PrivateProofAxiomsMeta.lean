import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.contains "directSumNeZeroMulEquiv._proof" then
      let ax ← collectAxioms n
      IO.println s!"{n}: axioms={ax.toList}"
