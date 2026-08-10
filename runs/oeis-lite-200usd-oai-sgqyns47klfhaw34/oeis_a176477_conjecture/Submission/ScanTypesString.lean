import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "A176477" || s.contains "176477" || s.contains "21" && s.contains "choose" && s.contains "32" then
      logInfo m!"decl {n} : {ci.type}"
      c:=c+1
  logInfo m!"count {c}"
