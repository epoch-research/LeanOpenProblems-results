import FormalConjectures.Util.ProblemImports
open Lean Elab Command
set_option maxHeartbeats 0
partial def exprHasNamePart (parts : Array String) : Expr → Bool
| .const n _ => parts.any (fun p => n.toString.contains p)
| .app f a => exprHasNamePart parts f || exprHasNamePart parts a
| .lam _ t b _ => exprHasNamePart parts t || exprHasNamePart parts b
| .forallE _ t b _ => exprHasNamePart parts t || exprHasNamePart parts b
| .letE _ t v b _ => exprHasNamePart parts t || exprHasNamePart parts v || exprHasNamePart parts b
| .mdata _ e => exprHasNamePart parts e
| .proj _ _ e => exprHasNamePart parts e
| _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut printed := 0
  for (n, ci) in env.constants.toList do
    if exprHasNamePart #["IsAlgebraic", "Transcendental", "algebraicClosure", "aeval"] ci.type then
      logInfo m!"{n}"
      printed := printed + 1
      if printed > 2000 then return
  logInfo m!"printed {printed}"
