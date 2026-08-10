import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if ns.contains "eventually" || ns.contains "Eventually" || ns.contains "IsBigO" || ns.contains "isBigO" || ns.contains "Tendsto" || ns.contains "tendsto" then
      if ns.contains "prime" || ns.contains "Prime" || ns.contains "Chebyshev" || ns.contains "theta" || ns.contains "psi" then
        arr := arr.push (ns ++ " : " ++ toString ci.type)
  arr := arr.qsort (fun a b => a < b)
  for s in arr do IO.println s
