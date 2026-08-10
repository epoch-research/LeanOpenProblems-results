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
  let falseTy := mkConst ``False
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    if !(resultHead ci.type).isConstOf ``False then continue
    let axs ← liftTermElabM <| collectAxioms name
    if !(axs.all allowedAx) then continue
    try
      liftTermElabM do
        let e ← mkAppM name #[]
        let e ← instantiateMVars e
        let ok ← isDefEq (← inferType e) falseTy
        if !ok then throwError "not false"
        let mvs ← getMVars e
        if !mvs.isEmpty then throwError "unassigned mvars {mvs}"
      logInfo m!"CLOSED_BY {name} : {ci.type} AX {axs.toList}"
      found := found + 1
    catch _ => pure ()
  logInfo m!"found {found}"
