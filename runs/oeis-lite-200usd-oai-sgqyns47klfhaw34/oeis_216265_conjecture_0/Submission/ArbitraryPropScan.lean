import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ts := toString ci.type
    if ts.contains "(P : Prop)" && (ts.endsWith " P" || ts.contains "-> P" || ts.contains "→ P") then
      IO.println s!"{n} : {ts}"
