import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let ty := ci.type
    if ty.isConstOf ``False then
      let axs ← collectAxioms n
      logInfo m!"FALSE {n} axioms {axs.toList}"
      count := count + 1
      if count > 50 then break
  logInfo m!"done {count}"
