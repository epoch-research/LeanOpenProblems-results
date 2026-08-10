import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if ns.contains "nth" || ns.contains "primeCounting" || ns.contains "Prime" then
      let ts := toString ci.type
      if ts.contains "nth" && (ts.contains "≤" || ts.contains "<" || ts.contains "primeCounting") then
        arr := arr.push (ns ++ " : " ++ ts)
  arr := arr.qsort (fun a b => a < b)
  for s in arr do IO.println s
