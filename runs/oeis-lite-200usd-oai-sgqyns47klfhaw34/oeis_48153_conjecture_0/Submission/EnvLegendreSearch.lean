import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    let s := toString t
    if (s.contains "legendreSym" || s.contains "quadraticChar" || s.contains "jacobiSym") && (s.contains "∑" || s.contains "sum" || s.contains "card" || s.contains "#") then
      arr := arr.push (toString n ++ " : " ++ s)
  for x in arr.qsort (· < ·) do
    logInfo x
