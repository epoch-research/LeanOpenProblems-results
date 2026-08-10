import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def containsFalse : Expr → Bool
  | .const `False [] => true
  | .forallE _ d b _ => containsFalse d || containsFalse b
  | .app f a => containsFalse f || containsFalse a
  | .lam _ d b _ => containsFalse d || containsFalse b
  | .letE _ t v b _ => containsFalse t || containsFalse v || containsFalse b
  | .mdata _ e => containsFalse e
  | .proj _ _ e => containsFalse e
  | _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    if containsFalse ci.type then
      arr := arr.push (toString n)
  arr := arr.qsort (· < ·)
  for s in arr[:200] do logInfo m!"{s}"
  logInfo m!"count {arr.size}"
