import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    let ts := toString ci.type
    if (ts.contains "Nat.nth Nat.Prime" || ts.contains "nth Nat.Prime" || ts.contains "primeGap") &&
       (ts.contains "≤" || ts.contains "<" || ts.contains "=" || ts.contains "Tendsto") then
      IO.println s!"{n} : {ts}"
