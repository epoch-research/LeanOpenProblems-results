import FormalConjectures.Util.ProblemImports
open Lean Meta

unsafe def isArrowToProp : Expr → Bool
| .forallE _ _ (.sort .zero) _ => true
| _ => false

unsafe def dangerousPredSearch : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    match t with
    | .forallE _ (.sort _) body1 _ =>
      match body1 with
      | .forallE _ dom2 body2 _ =>
        if isArrowToProp dom2 && (body2.isAppOf ``Exists || body2.isAppOf ``Subtype || body2.isAppOf ``Nonempty) then
          arr := arr.push (n,t)
      | _ => pure ()
    | _ => pure ()
  logInfo m!"dangerous exact-ish {arr.size}"
  for (n,t) in arr do logInfo m!"DANGER {n}: {t}"
#eval! dangerousPredSearch
