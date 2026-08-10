import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count > 100 then break
    let fmt ← liftCoreM <| Meta.MetaM.toIO (← readThe Core.Context) {} (ppExpr ci.type) -- maybe
    let ss := fmt.pretty
    if ss.contains "∀ {p : Prop}, p" || ss == "False" then
      logInfo m!"{n} : {fmt}"
      count := count + 1
  logInfo m!"count {count}"
