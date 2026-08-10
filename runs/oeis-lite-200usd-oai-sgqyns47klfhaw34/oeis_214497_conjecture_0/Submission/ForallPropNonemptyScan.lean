import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

partial def hasOuterPropAndResultNonemptyBVar : Expr → Bool
| .forallE _ dom body _ =>
  match dom with
  | .sort .zero =>
    let rec peel : Expr → Expr
    | .forallE _ _ b _ => peel b
    | e => e
    match peel body with
    | .app (.const ``Nonempty _) (.bvar 0) => true
    | .app (.const ``Inhabited _) (.bvar 0) => true
    | _ => false
  | _ => hasOuterPropAndResultNonemptyBVar body
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes then continue
    if hasOuterPropAndResultNonemptyBVar ci.type then
      let axs ← liftTermElabM <| collectAxioms name
      logInfo m!"ARBNE {name} unsafe={ci.isUnsafe} : {ci.type} AX {axs.toList}"
      found := found + 1
      if found > 100 then break
  logInfo m!"found {found}"
