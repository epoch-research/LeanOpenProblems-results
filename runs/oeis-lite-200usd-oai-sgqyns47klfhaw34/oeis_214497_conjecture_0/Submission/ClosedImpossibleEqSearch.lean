import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    if ci.type.isForall then continue
    let s := toString ci.type
    if s.contains "0 = 1" || s.contains "1 = 0" || s.contains "true = false" || s.contains "True = False" then
      let ax ← collectAxioms name
      if ax.all allowedAx then
        logInfo m!"{name}: {ci.type} AX {ax.toList}"
        shown := shown + 1
  logInfo m!"shown={shown}"
