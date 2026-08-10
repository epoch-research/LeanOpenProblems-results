import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#check (inferInstance : Subsingleton Prop)
#check (inferInstance : ∀ P : Prop, Subsingleton P)
-- expected failures below if uncommented:
-- #check (inferInstance : Nonempty False)
-- #check (inferInstance : Inhabited False)
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "Subsingleton Prop" || s.contains "Nonempty False" || s.contains "Inhabited False" || s.contains "∀ (P : Prop), P" || s.contains "∀ {P : Prop}, P" || s.contains "False →") then
      logInfo m!"{name} : {ci.type}"
