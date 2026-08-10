import FormalConjectures.Util.ProblemImports

open Lean Meta

unsafe def containsName (n : Name) : Expr → Bool
| .const m _ => m == n
| .app f a => containsName n f || containsName n a
| .lam _ t b _ => containsName n t || containsName n b
| .forallE _ t b _ => containsName n t || containsName n b
| .letE _ t v b _ => containsName n t || containsName n v || containsName n b
| .mdata _ e => containsName n e
| .proj _ _ e => containsName n e
| _ => false

unsafe def searchNonemptyDec : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if containsName ``Nonempty t && (containsName ``Decidable t || containsName ``Subsingleton t || containsName ``Unique t) then
      arr := arr.push (n,t)
  logInfo m!"candidates {arr.size}"
  for (n,t) in arr[:arr.size.min 500] do logInfo m!"NED {n}: {t}"
#eval! searchNonemptyDec
