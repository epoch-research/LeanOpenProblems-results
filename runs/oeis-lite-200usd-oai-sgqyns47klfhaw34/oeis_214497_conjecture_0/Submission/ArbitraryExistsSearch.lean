import FormalConjectures.Util.ProblemImports
open Lean Meta

unsafe def hasConst (n : Name) : Expr → Bool
| .const m _ => m == n
| .app f a => hasConst n f || hasConst n a
| .lam _ t b _ => hasConst n t || hasConst n b
| .forallE _ t b _ => hasConst n t || hasConst n b
| .letE _ t v b _ => hasConst n t || hasConst n v || hasConst n b
| .mdata _ e => hasConst n e
| .proj _ _ e => hasConst n e
| _ => false

unsafe def arbExistsSearch : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    -- log declarations whose tail after forall contains Exists/Subtype and whose first args are a Sort and a predicate-ish forall
    if hasConst ``Exists t || hasConst ``Subtype t then
      match t with
      | .forallE _ (.sort _) (.forallE _ dom2 body2 _) _ =>
        if hasConst ``Exists body2 || hasConst ``Subtype body2 then
          arr := arr.push (n,t)
      | _ => pure ()
  logInfo m!"arb-ish exists/subtype {arr.size}"
  for (n,t) in arr[:arr.size.min 400] do logInfo m!"ARBEX {n}: {t}"
#eval! arbExistsSearch
