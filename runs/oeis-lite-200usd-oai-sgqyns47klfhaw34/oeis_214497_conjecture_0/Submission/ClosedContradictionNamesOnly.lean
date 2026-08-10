import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes then continue
    let s := toString ci.type
    if s == "False" || s.contains "0 = 1" || s.contains "1 = 0" || s.contains "0 < 0" || s.contains "1 < 0" || s.contains "True = False" || s.contains "False = True" || s.contains "Nonempty False" || s.contains "Inhabited False" then
      logInfo m!"CAND {name} : {ci.type}"
      found := found + 1
      if found > 1000 then break
  logInfo m!"found {found}"
