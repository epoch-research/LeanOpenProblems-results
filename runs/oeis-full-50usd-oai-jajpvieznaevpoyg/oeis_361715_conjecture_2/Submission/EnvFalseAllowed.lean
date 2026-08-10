import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 50 then
      try
        let ty := ci.type
        if ty.isConstOf ``False then
          logInfo m!"false decl {n}"
          count := count + 1
      catch _ => pure ()
  logInfo m!"count {count}"
