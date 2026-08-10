import FormalConjectures.Util.ProblemImports

open Lean Meta
#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let ax ← collectAxioms n
    if ax.contains ``sorryAx then
      IO.println s!"{n} : {ci.type} AX {ax}"
      count := count + 1
      if count > 500 then break
  IO.println s!"count {count}"
