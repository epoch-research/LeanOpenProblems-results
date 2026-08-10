import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def containsConst (nm : Name) : Expr → Bool
| .const n _ => n == nm
| .app f a => containsConst nm f || containsConst nm a
| .lam _ t b _ => containsConst nm t || containsConst nm b
| .forallE _ t b _ => containsConst nm t || containsConst nm b
| .letE _ t v b _ => containsConst nm t || containsConst nm v || containsConst nm b
| .mdata _ b => containsConst nm b
| .proj _ _ b => containsConst nm b
| _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if containsConst ``False ci.type then
      logInfo m!"{n}: {ci.type}"
      c := c+1
      if c > 200 then break
  logInfo m!"count first {c}"
