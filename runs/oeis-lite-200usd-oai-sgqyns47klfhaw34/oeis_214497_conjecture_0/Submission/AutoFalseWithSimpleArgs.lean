import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command Term

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
  let falseTy := Lean.mkConst ``False
  let argStxs ← pure #[← `(0), ← `(1), ← `(2), ← `(3), ← `(True), ← `(False), ← `(Unit), ← `(PUnit), ← `(Bool), ← `(Empty), ← `(PEmpty), ← `(ℕ), ← `(ℤ), ← `(ℚ), ← `(Prop), ← `(Fin 0), ← `(Fin 1), ← `(Fin 2), ← `(ZMod 0), ← `(ZMod 1), ← `(ZMod 2)]
  let args ← liftTermElabM <| argStxs.mapM (fun stx => try elabTerm stx none catch _ => pure (Lean.mkConst ``Unit))
  let mut found : Nat := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    if !(resultHead ci.type).isConstOf ``False then continue
    let axs ← liftTermElabM <| collectAxioms name
    if !(axs.all allowedAx) then continue
    -- try zero and one explicit arg applications
    let argOpts : List (Option Expr) := [none] ++ (args.toList.map some)
    for a? in argOpts do
      try
        liftTermElabM do
          let e ← match a? with
            | none => mkAppM name #[]
            | some a => mkAppM name #[a]
          let ty ← inferType e
          let ok ← isDefEq ty falseTy
          if !ok then throwError "not false"
          let e ← instantiateMVars e
          let mvs ← getMVars e
          if !mvs.isEmpty then throwError "mvars"
        logInfo m!"FALSE_APP {name} arg={a?.isSome} : {ci.type} AX {axs.toList}"
        found := found + 1
      catch _ => pure ()
  logInfo m!"found {found}"
