import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (name, ci) in env.constants.toList do
    let t := ci.type
    if t.isConstOf ``False then
      c := c + 1
      logInfo m!"FALSE {name} : {ci.type}"
    if t.isAppOf ``Nonempty && t.getAppArgs.size == 1 && t.getAppArgs[0]!.isConstOf ``False then
      c := c + 1
      logInfo m!"NONEMPTY FALSE {name} : {ci.type}"
  logInfo m!"total {c}"
