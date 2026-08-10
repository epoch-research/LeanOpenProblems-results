import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def exprHasConst (needle : Name) : Expr → Bool
| .const n _ => n == needle
| .app f a => exprHasConst needle f || exprHasConst needle a
| .lam _ t b _ => exprHasConst needle t || exprHasConst needle b
| .forallE _ t b _ => exprHasConst needle t || exprHasConst needle b
| .letE _ t v b _ => exprHasConst needle t || exprHasConst needle v || exprHasConst needle b
| .mdata _ e => exprHasConst needle e
| .proj _ _ e => exprHasConst needle e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let t := ci.type
    if exprHasConst ``Nat.Prime t then
      let s := toString t
      if s.contains "∃" || s.contains "forall" || s.contains "∀" || s.contains "Infinite" || s.contains "Set.Infinite" then
        count := count + 1
        if shown < 300 then
          logInfo m!"{name} : {t}"
          shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
