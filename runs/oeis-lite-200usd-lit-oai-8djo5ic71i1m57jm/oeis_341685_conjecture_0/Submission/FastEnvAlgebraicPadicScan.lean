import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

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
  let mut n := 0
  for (name, ci) in env.constants.toList do
    if exprHasNamePart #["IsAlgebraic", "Transcendental"] ci.type && exprHasNamePart #["Padic", "tsum", "Summable"] ci.type then
      logInfo m!"{name} : {ci.type}"
      n := n + 1
      if n > 300 then
        logInfo m!"stopping"
        return
  logInfo m!"count {n}"
