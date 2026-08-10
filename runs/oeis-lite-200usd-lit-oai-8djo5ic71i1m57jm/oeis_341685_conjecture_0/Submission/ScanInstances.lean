import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let inst ← liftCoreM <| isInstance n
    if inst then
      let s := toString ci.type
      if s.contains "Infinite" || s.contains "Finite" || s.contains "Fintype" || s.contains "Subsingleton" || s.contains "Nontrivial" then
        logInfo m!"{n} : {ci.type}"
        count := count + 1
  logInfo m!"count {count}"
