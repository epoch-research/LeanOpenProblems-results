import FormalConjectures.Util.ProblemImports

open Lean

#eval show MetaM Unit from do
  let env ← getEnv
  let mut ax : Array Name := #[]
  for (n, c) in env.constants.toList do
    if c.isAxiom then
      ax := ax.push n
  IO.println ax
