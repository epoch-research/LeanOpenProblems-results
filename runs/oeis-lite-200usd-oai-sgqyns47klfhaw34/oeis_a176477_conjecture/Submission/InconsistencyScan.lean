import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let nonemptyFalse := mkApp (.const ``Nonempty [0]) (.const ``False [])
  let forallP := mkForall `P .default (.sort .zero) (.bvar 0)
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type.consumeMData
    if ty.isConstOf ``False || ty == nonemptyFalse || ty == forallP then
      logInfo m!"{n} : {ty}"
      cnt := cnt+1
  logInfo m!"count {cnt}"
