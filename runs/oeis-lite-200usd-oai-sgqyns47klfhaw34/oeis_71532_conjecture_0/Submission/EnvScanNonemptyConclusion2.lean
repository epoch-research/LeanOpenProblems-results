import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def finalExpr : Expr → Expr
| .forallE _ _ b _ => finalExpr b
| .mdata _ e => finalExpr e
| e => e

def headName? (e : Expr) : Option Name :=
  match e.getAppFn with | .const n _ => some n | _ => none

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c:=0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let res := finalExpr ci.type.consumeMData
    if headName? res == some ``Nonempty then
      let s := toString (← liftTermElabM <| ppExpr ci.type)
      logInfo m!"{n} : {s}"
      c:=c+1
      if c>300 then break
  logInfo m!"count {c}"
