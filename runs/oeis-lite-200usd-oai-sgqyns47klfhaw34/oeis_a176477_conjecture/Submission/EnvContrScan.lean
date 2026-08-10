import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "0 = 1" || s.contains "1 = 0" || s.contains "False" then
      if !(toString n).contains "not" then
        IO.println s!"{n} : {s}"
        count := count + 1
        if count > 200 then break
  IO.println s!"count {count}"
