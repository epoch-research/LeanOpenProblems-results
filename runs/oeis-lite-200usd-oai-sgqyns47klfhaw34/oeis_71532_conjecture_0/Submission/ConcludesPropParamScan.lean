import FormalConjectures.Util.ProblemImports
open Lean Elab Command

partial def finalConcl : Expr → Expr
| .forallE _ _ b _ => finalConcl b
| .mdata _ e => finalConcl e
| e => e

partial def hasConclBVar : Nat → Expr → Bool
| depth, .forallE _ (.sort .zero) b _ =>
    let c := finalConcl b
    -- this prop param has de Bruijn index 0 in body before entering later binders; after stripping all foralls, index increases by number of stripped binders; use toString fallback? no
    (toString c).contains "✝" || hasConclBVar (depth+1) b
| depth, .forallE _ _ b _ => hasConclBVar (depth+1) b
| _, _ => false

-- better: collect final conclusion string and print if type contains " : Prop"? keep manual limited
elab "#scan_concludes_prop" : command => do
  let env ← getEnv
  let mut c := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let s := toString ci.type
    -- final bits printed as parameter names are hard; grep common pattern
    if (s.contains " : Prop" || s.contains "{p : Prop}" || s.contains "{P : Prop}") &&
       !(s.contains "↔") && !(s.contains "=") then
      if s.contains "→ p" || s.contains "→ P" || s.endsWith " p" || s.endsWith " P" then
        if c < 300 then logInfo m!"{name} : {ci.type}"
        c := c+1
  logInfo m!"count {c}"
#scan_concludes_prop
