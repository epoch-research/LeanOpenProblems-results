import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

/-- crude detector: type has a Prop binder and final result is that binder, with at least one intervening forall/arrow. -/
partial def propBinderResultSameWithHyp : Expr → Bool
| .forallE _ dom body _ =>
  match dom with
  | .sort .zero =>
    let rec peelCount (c : Nat) : Expr → Nat × Expr
    | .forallE _ _ b _ => peelCount (c+1) b
    | e => (c,e)
    let (c,r) := peelCount 0 body
    match r with
    | .bvar i => i == 0 && c > 0
    | _ => false
  | _ => propBinderResultSameWithHyp body
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes then continue
    if propBinderResultSameWithHyp ci.type then
      let axs ← liftTermElabM <| collectAxioms name
      logInfo m!"WEAKARB {name} unsafe={ci.isUnsafe} : {ci.type} AX {axs.toList}"
      found := found + 1
      if found > 200 then break
  logInfo m!"found {found}"
