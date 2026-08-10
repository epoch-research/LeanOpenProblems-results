import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if ns.startsWith "Nat." || ns.startsWith "Chebyshev." || ns.startsWith "Set." || ns.startsWith "Filter." then
      let ts := toString ci.type
      if ts.contains "Prime" && (ts.contains "Set.I" || ts.contains "Finset.I" || ts.contains "primeCounting" || ts.contains "π" || ts.contains "atTop") && (ts.contains "∃" || ts.contains "≤" || ts.contains "<" || ts.contains "Tendsto" || ts.contains "Eventually") then
        IO.println s!"{n} : {ts}"
        c := c + 1
        if c > 800 then return ()
