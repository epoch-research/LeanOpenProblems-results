import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command Term
open Nat

abbrev Target214497 : Prop := ∀ n : ℕ, n > 0 →
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let target ← liftTermElabM <| elabType (← `(Target214497))
  let falseTy := Lean.mkConst ``False
  let nonemptyTarget ← liftTermElabM <| mkAppM ``Nonempty #[target]
  let shapes ← liftTermElabM do
    let impFT ← mkArrow falseTy target
    let impTF ← mkArrow target falseTy
    let notnot ← mkAppM ``Not #[← mkAppM ``Not #[target]]
    return #[target, ← mkAppM ``Not #[target], nonemptyTarget, impFT, impTF, notnot]
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    for idx in [0:shapes.size] do
      try
        liftTermElabM do
          let e ← mkAppM name #[]
          let ty ← inferType e
          let ok ← isDefEq ty shapes[idx]!
          if !ok then throwError "no"
          let e ← instantiateMVars e
          let mvs ← getMVars e
          if !mvs.isEmpty then throwError "mvars"
        let axs ← liftTermElabM <| collectAxioms name
        if axs.all allowedAx then
          logInfo m!"BRIDGE shape{idx} {name} : {ci.type} AX {axs.toList}"
          found := found + 1
      catch _ => pure ()
  logInfo m!"found {found}"
