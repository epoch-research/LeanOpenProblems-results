import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := #[]
  for (n, ci) in env.constants.toList do
    if found.size < 100 then
      let t := ci.type
      if t.isConstOf ``False then
        found := found.push n
  logInfo m!"False decls {found}"
