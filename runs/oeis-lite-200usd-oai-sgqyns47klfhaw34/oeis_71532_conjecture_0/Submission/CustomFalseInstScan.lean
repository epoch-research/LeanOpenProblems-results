import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "FormalConjecturesForMathlib" then
      let ty := toString ci.type
      if ty.contains "False" || ty.contains "Not" then
        IO.println s!"{n} : {ci.type}"
