import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ns := toString n
    let ts := toString ci.type
    if (ts.contains "Composite" || ts.contains "¬" && ts.contains "Prime" || ts.contains "smoothNumbers" || ts.contains "roughNumbers") &&
       (ts.contains "Finset.I" || ts.contains "Set.I" || ts.contains "consecutive" || ts.contains "∀" || ts.contains "Exists") then
      if ns.startsWith "Nat." || ns.startsWith "Finset." || ns.startsWith "Set." then
        IO.println s!"{n} : {ts}"
