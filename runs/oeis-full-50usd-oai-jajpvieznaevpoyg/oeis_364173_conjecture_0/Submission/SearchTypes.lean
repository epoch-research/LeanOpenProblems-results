import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def exprContainsConst (nm : Name) : Expr → Bool
| .const n _ => n == nm
| .app f a => exprContainsConst nm f || exprContainsConst nm a
| .lam _ t b _ => exprContainsConst nm t || exprContainsConst nm b
| .forallE _ t b _ => exprContainsConst nm t || exprContainsConst nm b
| .letE _ t v b _ => exprContainsConst nm t || exprContainsConst nm v || exprContainsConst nm b
| .mdata _ e => exprContainsConst nm e
| .proj _ _ e => exprContainsConst nm e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    if exprContainsConst ``Int.ModEq ty && (exprContainsConst ``Real.Gamma ty || exprContainsConst ``Classical.choose ty || exprContainsConst ``Set.range ty) then
      if count < 100 then logInfo m!"{n} : {ty}"
      count := count + 1
  logInfo m!"count {count}"
