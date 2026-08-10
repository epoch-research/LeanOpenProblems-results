import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n,ci) in env.constants.toList do
    let s := toString n
    let t := toString ci.type
    if (t.contains "^ 2" || t.contains "sq") && (t.contains "+" && t.contains "∃") then
      if t.contains "8" || t.contains "7" || s.contains "three" || s.contains "Three" || s.contains "Legendre" then
        arr := arr.push (s ++ " : " ++ t)
  for x in arr.qsort (· < ·) do logInfo x
