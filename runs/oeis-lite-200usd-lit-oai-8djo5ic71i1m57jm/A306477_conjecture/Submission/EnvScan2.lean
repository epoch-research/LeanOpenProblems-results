import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "Nonempty False" || s.contains "∀ (P : Prop), P" || s.contains "∀ P : Prop, P" || s.contains "False →" then
      logInfo m!"decl {n} : {ci.type}"
      c := c+1
      if c > 100 then break
  logInfo m!"count {c}"
