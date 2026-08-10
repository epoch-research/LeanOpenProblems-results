import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    let ts := toString ci.type
    if (ts.contains "Prime" || ns.contains "prime" || ns.contains "Prime") &&
       (ts.contains "/" || ts.contains "6" || ts.contains "5" || ts.contains "10" || ts.contains "512" || ts.contains "2 *" || ts.contains "+") &&
       (ts.contains "∃" || ts.contains "Exists" || ts.contains "≤" || ts.contains "<") then
      if ns.startsWith "Nat." || ns.startsWith "Bertrand" || ns.startsWith "Chebyshev" then
        IO.println s!"{n} : {ts}"
        c := c + 1
        if c > 1000 then return ()
