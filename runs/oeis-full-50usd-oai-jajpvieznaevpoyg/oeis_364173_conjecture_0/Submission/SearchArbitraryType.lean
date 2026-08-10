import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "∀ (P : Prop), P" || s.contains "∀ {P : Prop}, P" || s.contains "False" && (toString n).contains "choice" then
      if count < 100 then logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
