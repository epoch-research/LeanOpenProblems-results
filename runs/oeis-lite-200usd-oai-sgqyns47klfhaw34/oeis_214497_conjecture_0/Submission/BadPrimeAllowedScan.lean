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
  let badTypes ← liftTermElabM do
    let mut arr := #[]
    for n in [0,1,4,6,8,9,10,12,14,15,16,18,20,21,22,24,25,26,27,28,30] do
      arr := arr.push (← mkAppM ``Nat.Prime #[mkNatLit n])
    return arr
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    for t in badTypes do
      try
        liftTermElabM do
          let e ← mkAppM name #[]
          let ty ← inferType e
          let ok ← isDefEq ty t
          if !ok then throwError "no"
          let e ← instantiateMVars e
          let mvs ← getMVars e
          if !mvs.isEmpty then throwError "mvars"
        let axs ← liftTermElabM <| collectAxioms name
        if axs.all allowedAx then
          logInfo m!"BADPRIME {name} : {ci.type} AX {axs.toList}"
          found := found + 1
      catch _ => pure ()
  logInfo m!"found {found}"
