import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let bads := [`sorryAx, `lcProof, `lcCast, `Lean.ofReduceBool, `Lean.trustCompiler]
  let mut counts : Std.HashMap Name Nat := {}
  for (n, ci) in env.constants.toList do
    let ax ← collectAxioms n
    for b in bads do
      if ax.contains b then
        counts := counts.insert b ((counts.getD b 0)+1)
  for b in bads do logInfo m!"{b}: {counts.getD b 0}"
