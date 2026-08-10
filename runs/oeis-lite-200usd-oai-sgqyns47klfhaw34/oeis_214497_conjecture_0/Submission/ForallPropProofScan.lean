import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

/-- Detect a type beginning with forall P : Prop, ... result exactly the bound variable. -/
partial def resultIsOuterPropBVar : Expr → Bool
| .forallE _ dom body _ =>
  match dom with
  | .sort .zero =>
    let rec peel : Expr → Expr
    | .forallE _ _ b _ => peel b
    | e => e
    match peel body with
    | .bvar i => i == 0
    | _ => false
  | _ => resultIsOuterPropBVar body
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes then continue
    if resultIsOuterPropBVar ci.type then
      let axs ← liftTermElabM <| collectAxioms name
      logInfo m!"ARBPROP {name} unsafe={ci.isUnsafe} : {ci.type} AX {axs.toList}"
      found := found + 1
      if found > 100 then break
  logInfo m!"found {found}"
