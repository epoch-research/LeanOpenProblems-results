import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ts := toString ci.type
    if (ts.contains "Nonempty" && ts.contains "Prop") ||
       (ts.contains "(P : Prop)" && (ts.contains "Nonempty P" || ts.contains "¬¬" || ts.contains "Not (Not" || ts.contains " P")) then
      IO.println s!"{n} : {ts}"
      c := c + 1
      if c > 500 then return ()
