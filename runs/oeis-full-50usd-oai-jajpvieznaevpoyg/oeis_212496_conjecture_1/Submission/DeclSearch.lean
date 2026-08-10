import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "cardFactors" || s.contains "primeFactorsList" || s.contains "moebius" || s.contains "Squarefree") && (s.contains "sum" || s.contains "∑" || s.contains "<" || s.contains "≤") then
      IO.println s!"{n} : {ci.type}"
      count := count+1
      if count > 300 then return ()
  IO.println s!"count {count}"
