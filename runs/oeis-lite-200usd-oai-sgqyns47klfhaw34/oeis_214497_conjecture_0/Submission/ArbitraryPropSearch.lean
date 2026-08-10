import FormalConjectures.Util.ProblemImports

open Lean Meta

unsafe def isPropSort : Expr → Bool
| .sort .zero => true
| _ => false

unsafe def refersBVar0 : Expr → Bool
| .bvar 0 => true
| .app f a => refersBVar0 f || refersBVar0 a
| .lam _ t b _ => refersBVar0 t || refersBVar0 b
| .forallE _ t b _ => refersBVar0 t || refersBVar0 b
| .letE _ t v b _ => refersBVar0 t || refersBVar0 v || refersBVar0 b
| .mdata _ e => refersBVar0 e
| .proj _ _ e => refersBVar0 e
| _ => false

unsafe def arbSearch : CoreM Unit := do
  let env ← getEnv
  let mut arb := #[]
  let mut nonemptyTo := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    match t with
    | .forallE _ dom body _ =>
      if isPropSort dom then
        if body == .bvar 0 then arb := arb.push (n,t)
        -- ∀ P : Prop, Nonempty P -> P or P-ish
        match body with
        | .forallE _ dom2 body2 _ =>
          if body2 == .bvar 1 then nonemptyTo := nonemptyTo.push (n,t)
        | _ => pure ()
    | _ => pure ()
  logInfo m!"arb count {arb.size}"
  for (n,t) in arb do logInfo m!"ARB {n}: {t}"
  logInfo m!"nonempty-ish count {nonemptyTo.size}"
  for (n,t) in nonemptyTo[:nonemptyTo.size.min 100] do logInfo m!"NE {n}: {t}"

#eval! arbSearch
