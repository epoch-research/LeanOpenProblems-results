import FormalConjectures.Util.ProblemImports
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo val => IO.println s!"axiom {n} : {val.type}"
    | _ => pure ()
