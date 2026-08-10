import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def exprHasName (nm : Name) : Expr → Bool
| .const n _ => n == nm
| .app f a => exprHasName nm f || exprHasName nm a
| .lam _ t b _ => exprHasName nm t || exprHasName nm b
| .forallE _ t b _ => exprHasName nm t || exprHasName nm b
| .letE _ t v b _ => exprHasName nm t || exprHasName nm v || exprHasName nm b
| .mdata _ e => exprHasName nm e
| .proj _ _ e => exprHasName nm e
| _ => false
elab "#mine2" : command => do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    let ns := toString n
    let ts := toString ty
    if (exprHasName `Nat.smoothNumbers ty || ns.contains "smooth" || ns.contains "Smooth") &&
       (exprHasName `Nat.Prime ty || ns.contains "prime" || ns.contains "Prime" || ts.contains "Prime") then
      logInfo m!"{n} : {ty}"
#mine2
