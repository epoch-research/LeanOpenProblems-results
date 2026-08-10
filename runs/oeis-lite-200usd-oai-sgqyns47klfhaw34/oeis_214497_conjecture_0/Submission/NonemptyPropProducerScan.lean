import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    let s := toString ci.type
    if (s.contains "Nonempty" || s.contains "Inhabited") && s.contains "Prop" then
      let axs ← liftTermElabM <| collectAxioms name
      if axs.all allowedAx then
        logInfo m!"NEP {name} : {ci.type} AX {axs.toList}"
        found := found + 1
        if found > 400 then break
  logInfo m!"found {found}"
