import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes then continue
    let type := ci.type
    let s := toString type
    if s == "False" || s.contains "0 = 1" || s.contains "1 = 0" || s.contains "0 < 0" || s.contains "1 < 0" || s.contains "True = False" || s.contains "False = True" || s.contains "Nonempty False" || s.contains "Inhabited False" then
      let axs ← liftTermElabM <| collectAxioms name
      let okAx := axs.all (fun a => allowed.contains a)
      if !okAx then continue
      logInfo m!"CAND {name} : {type}\n axioms={axs.toList}"
      found := found + 1
      if found > 500 then break
  logInfo m!"found {found}"
