import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr : Array (Name × Expr) := #[]
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "Infinite" then arr := arr.push (n, ci.type)
  let sorted := arr.qsort (fun a b => toString a.1 < toString b.1)
  for (n,t) in sorted.extract 0 (min sorted.size 400) do logInfo m!"{n} : {t}"
  logInfo m!"count={sorted.size}"
