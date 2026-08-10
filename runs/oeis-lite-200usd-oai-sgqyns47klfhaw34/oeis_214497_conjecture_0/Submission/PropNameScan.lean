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
    let ns := toString name
    if ns.contains "prop" || ns.contains "Prop" || ns.contains "proof_irrel" || ns.contains "propext" || ns.contains "subsingleton" || ns.contains "Subsingleton" then
      let axs ← liftTermElabM <| collectAxioms name
      if axs.all allowedAx then
        if found < 400 then logInfo m!"PNAME {name} : {ci.type} AX {axs.toList}"
        found := found + 1
  logInfo m!"found {found}"
