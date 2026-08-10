import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "#name_scan_padic_alg" : command => do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if count < 500 && ((s.contains "Padic" || s.contains "padic" || s.contains "Cauchy" || s.contains "CauSeq") && (s.contains "Algebra" || s.contains "algebra" || s.contains "Trans" || s.contains "trans" || s.contains "finite" || s.contains "Finite" || s.contains "integral" || s.contains "Integral" || s.contains "summ" || s.contains "Summ")) then
      logWarning m!"{n} : {ci.type}"
      count := count + 1
  logWarning m!"printed {count}"
#name_scan_padic_alg
