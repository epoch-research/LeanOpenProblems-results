import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def badShape (e : Expr) : Bool :=
  match e with
  | .forallE _ (.sort _) body _ =>
      match body with
      | .bvar 0 => true
      | .sort _ => false
      | _ => badShape body
  | .forallE _ _ body _ => badShape body
  | _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := #[]
  for (n, ci) in env.constants.toList do
    if found.size < 100 && badShape ci.type then found := found.push (n, ci.type)
  for (n,t) in found do logInfo m!"{n}: {t}"
