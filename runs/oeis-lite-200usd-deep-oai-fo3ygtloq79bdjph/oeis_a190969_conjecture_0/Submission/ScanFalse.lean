import FormalConjectures.Util.ProblemImports

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t.isConstOf ``False then
      IO.println s!"{n} : {t}"
