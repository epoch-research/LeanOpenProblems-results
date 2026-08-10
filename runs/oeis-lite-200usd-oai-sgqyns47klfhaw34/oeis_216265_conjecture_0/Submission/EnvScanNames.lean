import FormalConjectures.Util.ProblemImports
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if (ns.contains "prime" || ns.contains "Prime" || ns.contains "Chebyshev" || ns.contains "Bertrand" || ns.contains "count") &&
       (ns.contains "exists" || ns.contains "le" || ns.contains "lt" || ns.contains "bound" || ns.contains "Counting" || ns.contains "gap" || ns.contains "Gap" || ns.contains "tendsto" || ns.contains "theta") then
      arr := arr.push ns
  arr := arr.qsort (fun a b => a < b)
  for s in arr do
    IO.println s
