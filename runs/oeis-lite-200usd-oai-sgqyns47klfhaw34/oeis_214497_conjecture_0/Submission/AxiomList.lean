import FormalConjectures.Util.ProblemImports
open Lean Meta
unsafe def axiomList : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo v => arr := arr.push (n, v.type)
    | _ => pure ()
  logInfo m!"axioms {arr.size}"
  for (n,t) in arr do logInfo m!"AX {n}: {t}"
#eval! axiomList
