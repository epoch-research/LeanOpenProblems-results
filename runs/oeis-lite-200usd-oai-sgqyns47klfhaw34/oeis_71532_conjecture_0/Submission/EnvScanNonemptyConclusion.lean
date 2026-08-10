import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def resultHead : Expr → Expr
| .forallE _ _ b _ => resultHead b
| e => e.getAppFn

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c:=0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let t:=ci.type.consumeMData
    if resultHead t == mkConst ``Nonempty then
      let s := toString (← liftTermElabM <| ppExpr t)
      -- skip constructors and obvious ones? print first 300
      if !(toString n).contains "inst" || s.contains "→ Nonempty" then
        logInfo m!"{n} : {s}"
        c:=c+1
        if c>300 then break
  logInfo m!"count {c}"
