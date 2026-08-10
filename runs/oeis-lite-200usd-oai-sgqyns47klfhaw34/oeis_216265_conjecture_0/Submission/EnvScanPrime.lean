import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def relevantName (s : String) : Bool :=
  (s.contains "prime" || s.contains "Prime" || s.contains "Chebyshev" || s.contains "Bertrand" || s.contains "count") &&
  !(s.contains "Polynomial") && !(s.contains "Ideal") && !(s.contains "Spectrum") && !(s.contains "Submodule")

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let ns := n.toString
    if relevantName ns then
      let ts := toString ci.type
      if (ts.contains "Nat.Prime" || ts.contains "Prime" || ts.contains "primeCounting" || ts.contains "count") &&
         (ts.contains "∃" || ts.contains "∀" || ts.contains "<" || ts.contains "≤") then
        arr := arr.push (ns ++ " : " ++ ts)
  arr := arr.qsort (fun a b => a < b)
  for s in arr do
    if s.contains "Nat.Prime" || s.contains "primeCounting" || s.contains "exists_prime" || s.contains "Bertrand" || s.contains "Chebyshev" then
      logInfo s
