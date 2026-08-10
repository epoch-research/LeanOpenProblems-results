import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "#scan_closed_integral_names" : command => unsafe do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (s.contains "Closed" || s.contains "closed" || s.contains "closure") && (s.contains "Integral" || s.contains "integral" || s.contains "Algebraic" || s.contains "algebraic") then
      IO.println s!"{n} : {ci.type}"
#scan_closed_integral_names
