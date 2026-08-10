import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t.isConstOf `False then
      IO.println s!"literal False: {n} : {t}"
      c := c + 1
      if c > 50 then break
  IO.println s!"count first {c}"
