import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
partial def hasFalseConst : Expr → Bool
  | .const ``False _ => true
  | .forallE _ d b _ => hasFalseConst d || hasFalseConst b
  | .app f a => hasFalseConst f || hasFalseConst a
  | .lam _ d b _ => hasFalseConst d || hasFalseConst b
  | .letE _ t v b _ => hasFalseConst t || hasFalseConst v || hasFalseConst b
  | .mdata _ e => hasFalseConst e
  | .proj _ _ e => hasFalseConst e
  | _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut c := 0
  for (n, ci) in env.constants.toList do
    if hasFalseConst ci.type then
      logInfo m!"{n} : {ci.type}"
      c := c + 1
      if c >= 200 then break
  logInfo m!"count {c}"
