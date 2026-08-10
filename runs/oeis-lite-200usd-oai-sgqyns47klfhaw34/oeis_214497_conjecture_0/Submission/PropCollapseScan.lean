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
  let patterns := ["Subsingleton Prop", "Prop =", "= Prop", "True = False", "False = True", "proof_irrel", "not_subsingleton Prop", "Prop ≃ Bool", "IsEmpty Prop"]
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    let s := toString ci.type
    if patterns.any (fun p => s.contains p) || (toString name).contains "prop" || (toString name).contains "Prop" then
      let axs ← liftTermElabM <| collectAxioms name
      if axs.all allowedAx then
        if found < 500 then logInfo m!"PCOLL {name} : {ci.type} AX {axs.toList}"
        found := found + 1
  logInfo m!"found {found}"
