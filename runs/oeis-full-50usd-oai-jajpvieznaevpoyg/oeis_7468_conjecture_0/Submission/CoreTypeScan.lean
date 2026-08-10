import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def hasConst (c : Name) : Expr → Bool
| .const n _ => n == c
| .app f a => hasConst c f || hasConst c a
| .lam _ t b _ => hasConst c t || hasConst c b
| .forallE _ t b _ => hasConst c t || hasConst c b
| .letE _ t v b _ => hasConst c t || hasConst c v || hasConst c b
| .mdata _ e => hasConst c e
| .proj _ _ e => hasConst c e
| _ => false

elab "#core_scan" : command => do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      if hasConst ``False ti.type || hasConst ``Subsingleton ti.type then
        let fmt ← liftTermElabM <| ppExpr ti.type
        let s := toString fmt
        if s.contains "False" || s.contains "Subsingleton ℕ" || s.contains "Nat" then
          logInfo m!"{n} : {fmt}"
          count := count + 1
          if count > 200 then break
    | _ => pure ()
  logInfo m!"count {count}"
#core_scan
