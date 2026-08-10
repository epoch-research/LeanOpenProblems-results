import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    if (toString n).contains "_proof" then continue
    let t := toString ci.type
    if (t.contains "^ 2 +" && (t.contains "+ c ^ 2" || t.contains "+ z ^ 2" || t.contains "+ d ^ 2")) || (t.contains "sq_add" && t.contains "sq") then
      arr := arr.push (toString n ++ " : " ++ t.take 300)
  IO.println s!"count {arr.size}"
  for s in (arr.qsort (· < ·)).take 300 do IO.println s
