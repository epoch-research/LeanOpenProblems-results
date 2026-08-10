import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let ax ← collectAxioms n
    if ax.contains `sorryAx then
      IO.println s!"{n} : {ci.type}"
      c := c + 1
      if c > 50 then break
  IO.println s!"count shown {c}"
