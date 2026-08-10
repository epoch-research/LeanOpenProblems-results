import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      if ti.type == .const `False [] then
        IO.println s!"{n}"
        count := count + 1
    | _ => pure ()
  IO.println s!"count {count}"
