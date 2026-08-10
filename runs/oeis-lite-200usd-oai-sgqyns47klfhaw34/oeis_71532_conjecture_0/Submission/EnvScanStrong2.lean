import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def occursConst (nm : Name) : Expr → Bool
| .const n _ => n == nm
| .app f a => occursConst nm f || occursConst nm a
| .lam _ t b _ => occursConst nm t || occursConst nm b
| .forallE _ t b _ => occursConst nm t || occursConst nm b
| .letE _ t v b _ => occursConst nm t || occursConst nm v || occursConst nm b
| .mdata _ e => occursConst nm e
| .proj _ _ e => occursConst nm e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let falseExpr := mkConst ``False
  let emptyExpr := mkConst ``Empty
  let pemptyExpr := mkConst ``PEmpty
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let t := ci.type.consumeMData
    if t == falseExpr || occursConst ``False t || occursConst ``Empty t || occursConst ``PEmpty t then
      let s := toString (← liftTermElabM <| ppExpr t)
      if s == "False" || s.contains "Nonempty Empty" || s.contains "Nonempty PEmpty" || s.contains "Inhabited False" || s.contains "Inhabited Empty" || s.contains "False →" || s.contains "→ False" then
        logInfo m!"{n} : {s}"
        count := count + 1
        if count > 300 then break
  logInfo m!"count={count}"
