import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo _ => arr := arr.push n
    | .opaqueInfo _ => arr := arr.push n
    | _ => pure ()
  arr := arr.qsort (toString · < toString ·)
  for n in arr do logInfo m!"{n}"
