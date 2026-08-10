import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    let ts := toString ci.type
    if ns.contains "exists_prime" || (ts.contains "∃" && ts.contains "Nat.Prime") then
      arr := arr.push (ns ++ " : " ++ ts)
  arr := arr.qsort (fun a b => a < b)
  for s in arr do IO.println s
