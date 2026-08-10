import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def final : Expr → Expr
| .forallE _ _ b _ => final b
| .mdata _ e => final e
| e => e

def hasConst (nm : Name) : Expr → Bool
| .const n _ => n == nm
| .app f a => hasConst nm f || hasConst nm a
| .forallE _ d b _ => hasConst nm d || hasConst nm b
| .lam _ d b _ => hasConst nm d || hasConst nm b
| .letE _ t v b _ => hasConst nm t || hasConst nm v || hasConst nm b
| .mdata _ e => hasConst nm e
| .proj _ _ e => hasConst nm e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c:=0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let res := final ci.type.consumeMData
    if (match res.getAppFn with | .const nm _ => nm == ``Nonempty | _ => false) then
      let s := toString (← liftTermElabM <| ppExpr ci.type)
      if !(s.contains "[Nonempty") && !(s.contains "Nonempty α]") && !(s.contains "→ Nonempty α") then
        if s.contains "Nonempty α" || s.contains "Nonempty ↥" || s.contains "Nonempty Empty" || s.contains "Nonempty (" then
          logInfo m!"{n} : {s}"
          c:=c+1
          if c>400 then break
  logInfo m!"count={c}"
