import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

partial def resultHead : Expr → Expr
| .forallE _ _ b _ => resultHead b
| e => e

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
    let r := resultHead ci.type
    if r.isConstOf ``False then
      let axs ← liftTermElabM <| collectAxioms name
      if axs.all allowedAx then
        logInfo m!"FALSE_RESULT {name} : {ci.type} AX {axs.toList}"
        found := found + 1
        if found > 500 then break
  logInfo m!"found {found}"
