import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let keys := ["IsAlgebraic", "Transcendental", "Padic", "padic", "FiniteDimensional", "NumberField", "IsQuadratic", "IsField", "algebraicClosure", "not_isAlgebraic", "isAlgebraic", "false", "False", "det", "rank", "finrank"]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ns := toString n
    if keys.any (fun k => ns.contains k) then
      logInfo m!"{n} : {ci.type}"
      count := count + 1
      if count > 3000 then break
  logInfo m!"printed {count}"
