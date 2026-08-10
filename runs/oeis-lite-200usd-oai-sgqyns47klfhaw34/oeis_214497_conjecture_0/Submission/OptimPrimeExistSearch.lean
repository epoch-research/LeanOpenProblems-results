import FormalConjectures.Util.ProblemImports
open Lean Elab Command

partial def mentionsConst (needle : Name) : Expr → Bool
| .const n _ => n == needle
| .app f a => mentionsConst needle f || mentionsConst needle a
| .lam _ t b _ => mentionsConst needle t || mentionsConst needle b
| .forallE _ t b _ => mentionsConst needle t || mentionsConst needle b
| .letE _ t v b _ => mentionsConst needle t || mentionsConst needle v || mentionsConst needle b
| .mdata _ e => mentionsConst needle e
| .proj _ _ e => mentionsConst needle e
| _ => false

partial def finalResult : Expr → Expr
| .forallE _ _ b _ => finalResult b
| e => e

partial def hasExists : Expr → Bool
| .app (.app (.const ``Exists _) _) _ => true
| .app f a => hasExists f || hasExists a
| .lam _ t b _ => hasExists t || hasExists b
| .forallE _ t b _ => hasExists t || hasExists b
| .letE _ t v b _ => hasExists t || hasExists v || hasExists b
| .mdata _ e => hasExists e
| .proj _ _ e => hasExists e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr : Array (Name × Expr) := #[]
  for (name, ci) in env.constants.toList do
    let ty := ci.type
    if mentionsConst ``Nat.Prime ty && hasExists (finalResult ty) then
      arr := arr.push (name, ty)
  let sorted := arr.qsort (fun a b => toString a.1 < toString b.1)
  for (name, ty) in sorted.extract 0 (min sorted.size 500) do
    logInfo m!"{name} : {ty}"
  logInfo m!"count={sorted.size}"
