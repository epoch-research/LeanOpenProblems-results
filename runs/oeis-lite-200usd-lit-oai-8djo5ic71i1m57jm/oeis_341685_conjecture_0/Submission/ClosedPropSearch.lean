import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#closed_prop_search" : command => do
  let env ← getEnv
  let mut count := 0
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if printed >= 200 then break
    if n.isInternal then continue
    let type := ci.type
    let isProp ← liftTermElabM <| Meta.isProp type
    if isProp then
      count := count + 1
      let t := type.consumeMData
      let bad :=
        t.isConstOf ``False ||
        (match t with
         | Expr.app (Expr.const ``Not _) a => a.consumeMData.isConstOf ``True
         | _ => false)
      if bad then
        let pp ← liftTermElabM <| Meta.ppExpr type
        logInfo m!"CAND {n} : {pp}"
        printed := printed + 1
  logInfo m!"closed prop count {count}, printed {printed}"

#closed_prop_search
