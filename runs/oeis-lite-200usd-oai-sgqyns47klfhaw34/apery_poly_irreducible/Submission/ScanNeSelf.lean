import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def resultType : Expr → Expr
| .forallE _ _ b _ => resultType b
| e => e
#eval! show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if c < 100 then
      let r := resultType ci.type
      match r with
      | .app (.app (.app (.const ``Ne _) _) a) b =>
          if a == b then
            logInfo m!"{n} : {ci.type}"
            c := c+1
      | _ => pure ()
  logInfo m!"count {c}"
