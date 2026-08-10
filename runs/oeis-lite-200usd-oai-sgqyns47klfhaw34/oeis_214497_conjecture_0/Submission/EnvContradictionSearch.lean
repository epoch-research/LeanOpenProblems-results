import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut countFalse := 0
  let mut countForallP := 0
  for (name, ci) in env.constants.toList do
    let ty := ci.type
    if ty.isConstOf ``False then
      logInfo m!"FALSE_DECL {name} : {ty}"
      countFalse := countFalse + 1
    -- look for forall P : Prop, P by string as a lightweight filter
    let s := toString ty
    if s.contains "∀" && s.contains "Prop" && s.endsWith "P" then
      if s.contains "P : Prop" then
        logInfo m!"PROP_DECL? {name} : {ty}"
        countForallP := countForallP + 1
  logInfo m!"counts false={countFalse} forallP?={countForallP}"
