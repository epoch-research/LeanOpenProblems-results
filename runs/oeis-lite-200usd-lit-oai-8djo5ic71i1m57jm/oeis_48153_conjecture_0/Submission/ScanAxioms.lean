import FormalConjectures.Util.ProblemImports
open Lean
partial def hasConst (target : Name) : Expr → Bool
| Expr.const n _ => n == target
| Expr.app f a => hasConst target f || hasConst target a
| Expr.lam _ t b _ => hasConst target t || hasConst target b
| Expr.forallE _ t b _ => hasConst target t || hasConst target b
| Expr.letE _ t v b _ => hasConst target t || hasConst target v || hasConst target b
| Expr.mdata _ b => hasConst target b
| Expr.proj _ _ b => hasConst target b
| _ => false
#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if count < 100 then
      let typeConsts := hasConst ``sorryAx ci.type
      let valConsts := match ci.value? with | some v => hasConst ``sorryAx v | none => false
      if typeConsts || valConsts then
        IO.println s!"sorry dep {n}"
        count := count + 1
  IO.println s!"count first {count}"
