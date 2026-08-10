import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta
#eval show CommandElabM Unit from do
  let env ← getEnv
  let u := Level.zero
  let target := mkForall `P .default (mkSort u) (mkBVar 0)
  let mut found := 0
  for (n, ci) in env.constants.toList do
    try
      let eq ← liftTermElabM <| isDefEq ci.type target
      if eq then
        logInfo m!"forall prop theorem: {n}"
        found := found + 1
    catch _ => pure ()
  logInfo m!"found {found}"
