import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.constants.toList.map (·.1)
  for n in names do
    let ci := env.constants.find! n
    let s := toString ci.type
    if s.contains "∀ (P : Prop), P" || s.contains "Nonempty False" || s.contains "False →" then
      IO.println s!"{n} : {ci.type}"
