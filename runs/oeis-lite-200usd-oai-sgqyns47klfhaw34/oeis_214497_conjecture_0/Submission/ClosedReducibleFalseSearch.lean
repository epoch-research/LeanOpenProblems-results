import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

elab "#closed_reducible_false_search" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    let mut checked := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      -- closed declarations only: no forall binders
      if ci.type.isForall then continue
      let s := toString ci.type
      if !(s.contains "False" || s.contains "0 = 1" || s.contains "1 = 0" || s.contains "True = False" || s.contains "Fin 0" || s.contains "Empty") then continue
      checked := checked + 1
      let ty ← whnf ci.type
      if ty.isConstOf ``False || toString ty == "False" then
        let ax ← collectAxioms name
        if ax.all allowedAx then
          logInfo m!"HIT {name}: {ci.type} whnf {ty} AX {ax.toList}"
          shown := shown + 1
    logInfo m!"checked={checked} shown={shown}"

#closed_reducible_false_search
