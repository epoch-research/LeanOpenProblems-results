import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo ai =>
      if !ai.isUnsafe then IO.println s!"SAFE AXIOM {n} : {ai.type}"
    | _ => pure ()
