import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 200 then
      let s := toString ci.type
      if (s.contains "Odd" && (s.contains "^" || s.contains "pow" || s.contains "digits" || s.contains "choose")) then
        logInfo m!"{n} : {ci.type}"
        count := count + 1
