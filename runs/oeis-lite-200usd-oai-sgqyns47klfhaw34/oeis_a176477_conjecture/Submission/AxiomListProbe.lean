import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .axiomInfo v => arr := arr.push (n, v.type)
    | _ => pure ()
  logInfo m!"axioms count {arr.size}"
  for (n,t) in arr.qsort (fun a b => toString a.1 < toString b.1) do
    if (toString n).contains "lc" || (toString n).contains "choice" || (toString n).contains "sound" || n == `propext then
      logInfo m!"{n}: {t}"
