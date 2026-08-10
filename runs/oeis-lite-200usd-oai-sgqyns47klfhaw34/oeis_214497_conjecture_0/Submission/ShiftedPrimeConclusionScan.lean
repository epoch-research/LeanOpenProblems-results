import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def resultAfterForall : Expr → Expr
  | Expr.forallE _ _ b _ => resultAfterForall b
  | e => e

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    if shown < 100 then
      let r := resultAfterForall ci.type
      if r.isAppOf ``Nat.Prime then
        let s := toString ci.type
        if s.contains "+ 1" || s.contains "+ 2" || s.contains "succ" || s.contains "pred" then
          shown := shown + 1
          logInfo m!"{n} : {ci.type}"
  logInfo m!"shown {shown}"
