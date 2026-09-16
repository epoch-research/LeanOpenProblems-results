import FormalConjectures.Util.ProblemImports

open Lean

#eval show MetaM Unit from do
  let env ← getEnv
  let mut sorries : Array Name := #[]
  for (n, c) in env.constants.toList do
    let ax := env.getModuleIdxFor? n
    if ax.isSome then
      let deps := c.type.getUsedConstants
      -- this doesn't get proof dependencies.
      pure ()
  IO.println "Done"
