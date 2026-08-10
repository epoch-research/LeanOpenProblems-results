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
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe || ci.type.isForall then continue
    let s := toString ci.type
    if s.contains "= ¬" || s.contains "¬" && s.contains " = " || s.contains "True = False" || s.contains "False = True" || s.contains "0 = 1" || s.contains "1 = 0" then
      let axs ← liftTermElabM <| collectAxioms name
      if axs.all allowedAx then
        logInfo m!"WEIRDEQ {name} : {ci.type} AX {axs.toList}"
        found := found + 1
        if found > 200 then break
  logInfo m!"found {found}"
