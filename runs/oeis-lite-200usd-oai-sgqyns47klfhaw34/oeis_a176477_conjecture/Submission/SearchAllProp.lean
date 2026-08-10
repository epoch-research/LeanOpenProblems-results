import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def hasForallPropToVar (e : Expr) : Bool :=
  match e with
  | .forallE _ (.sort .zero) body _ =>
    match body with
    | .bvar 0 => true
    | _ => hasForallPropToVar body
  | .forallE _ _ body _ => hasForallPropToVar body
  | _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := #[]
  for (n, ci) in env.constants.toList do
    if found.size < 50 && hasForallPropToVar ci.type then found := found.push (n, ci.type)
  for x in found do logInfo m!"{x.1} : {x.2}"
