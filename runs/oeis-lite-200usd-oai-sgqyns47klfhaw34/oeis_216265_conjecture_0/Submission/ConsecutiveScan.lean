import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if ns.contains "Factorial" || ns.contains "factorial" || ns.contains "choose" || ns.contains "primeFactors" then
      let ts := toString ci.type
      if (ts.contains "Nat.Prime" || ts.contains "Prime" || ts.contains "primeFactors") && (ts.contains "∃" || ts.contains "∀" || ts.contains "∣" || ts.contains "<" || ts.contains "≤") then
        arr := arr.push (ns ++ " : " ++ ts)
  arr := arr.qsort (fun a b => a < b)
  for s in arr[:min arr.size 800] do IO.println s
