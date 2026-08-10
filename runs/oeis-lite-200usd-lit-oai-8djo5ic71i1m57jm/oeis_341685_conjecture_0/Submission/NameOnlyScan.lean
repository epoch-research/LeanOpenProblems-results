import FormalConjectures.Util.ProblemImports
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let keys := #["Padic", "padic", "IsAlgebraic", "Transcendental", "NumberField", "FiniteDimensional", "IsField", "xi", "factorial"]
  let mut arr : Array Name := #[]
  for (n, _) in env.constants.toList do
    let s := toString n
    if keys.any (fun k => s.contains k) then
      arr := arr.push n
  logInfo m!"found {arr.size}"
  for n in arr.qsort (fun a b => toString a < toString b) do
    logInfo m!"{n}"
