import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut xs := #[]
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "Quot" || s.contains "quot" then
      xs := xs.push (n, toString ci.type)
  for (n,t) in xs do
    if (t.contains "=" && (t.contains "→" || t.contains "->")) || (toString n).contains "exact" || (toString n).contains "sound" || (toString n).contains "rel" then
      logInfo m!"{n} : {t}"
