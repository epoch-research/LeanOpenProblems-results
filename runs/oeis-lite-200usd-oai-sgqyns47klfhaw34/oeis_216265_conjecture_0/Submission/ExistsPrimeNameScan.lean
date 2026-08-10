import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if ns.contains "exists_prime" || ns.contains "infinite_primes" || ns.contains "prime_gt" || ns.contains "prime_lt" then
      arr := arr.push (ns ++ " : " ++ toString ci.type)
  arr := arr.qsort (fun a b => a < b)
  for s in arr do IO.println s
