import FormalConjectures.Util.ProblemImports
import Lean
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let axs ← collectAxioms n
    if axs.contains `lcProof then
      logInfo m!"LC {n} : {ci.type}"
      count := count + 1
      if count > 100 then break
  logInfo m!"count {count}"
