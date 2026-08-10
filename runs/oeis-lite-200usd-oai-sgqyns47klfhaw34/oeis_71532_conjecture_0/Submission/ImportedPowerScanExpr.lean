import FormalConjectures.Util.ProblemImports
open Lean Elab Command

partial def hasBadShape : Expr → Bool
| .const ``False _ => true
| .forallE _ (.sort .zero) b _ =>
    -- body may be de Bruijn var 0: ∀ P:Prop, P ; or recursively
    match b with
    | .bvar 0 => true
    | _ => hasBadShape b
| .forallE _ _ b _ => hasBadShape b
| .app (.const ``Nonempty _) (.const ``False _) => true
| .app (.const ``Inhabited _) (.const ``False _) => true
| _ => false

elab "#scan_power_expr" : command => do
  let env ← getEnv
  let mut c := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    if hasBadShape ci.type then
      if c < 300 then logInfo m!"{name} : {ci.type}"
      c := c + 1
  logInfo m!"count {c}"

#scan_power_expr
