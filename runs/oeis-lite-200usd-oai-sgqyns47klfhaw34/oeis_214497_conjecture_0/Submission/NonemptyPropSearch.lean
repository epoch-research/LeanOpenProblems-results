import FormalConjectures.Util.ProblemImports

open Lean Meta

unsafe def containsConst (n : Name) : Expr → Bool
| .const m _ => m == n
| .app f a => containsConst n f || containsConst n a
| .lam _ t b _ => containsConst n t || containsConst n b
| .forallE _ t b _ => containsConst n t || containsConst n b
| .letE _ t v b _ => containsConst n t || containsConst n v || containsConst n b
| .mdata _ e => containsConst n e
| .proj _ _ e => containsConst n e
| _ => false

unsafe def nePropSearch : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    match t with
    | .forallE _ (.sort .zero) body _ =>
      if containsConst ``Nonempty body then arr := arr.push (n,t)
    | _ => pure ()
  logInfo m!"forall Prop producing Nonempty count {arr.size}"
  for (n,t) in arr[:arr.size.min 200] do logInfo m!"NEPROD {n}: {t}"

#eval! nePropSearch
