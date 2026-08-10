import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let pats := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "∀ (P : Prop), P") || (s.contains "Nonempty P") || (s.contains "False →") then
      IO.println s!"{n} : {ci.type}"
      count := count + 1
      if count > 100 then break
