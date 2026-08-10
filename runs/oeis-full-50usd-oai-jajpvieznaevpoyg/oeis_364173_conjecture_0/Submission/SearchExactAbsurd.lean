import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta

#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : Array String := #["0 = 1", "Subsingleton ℤ", "Subsingleton ℝ", "False"]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if targets.any (fun t => s == t) then
      logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
