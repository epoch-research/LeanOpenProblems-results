import FormalConjectures.Util.ProblemImports
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo ai =>
        count := count + 1
        if count < 300 then IO.println s!"AXIOM {n} unsafe={ai.isUnsafe} type={ai.type}"
    | _ => pure ()
  IO.println s!"axiom count {count}"
