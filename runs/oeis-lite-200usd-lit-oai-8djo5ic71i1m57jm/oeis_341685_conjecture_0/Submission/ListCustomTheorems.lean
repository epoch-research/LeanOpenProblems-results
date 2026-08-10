import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if s.startsWith "FormalConjecturesForMathlib" || s.startsWith "Set." || s.startsWith "Nat." || s.startsWith "SimpleGraph." || s.startsWith "Polynomial." || s.startsWith "Cardinal." || s.startsWith "ZMod." then
      match ci with
      | .thmInfo ti =>
          if ti.type.hasSorry then pure () else
          logInfo m!"THM {n} : {ti.type}"
      | _ => pure ()
