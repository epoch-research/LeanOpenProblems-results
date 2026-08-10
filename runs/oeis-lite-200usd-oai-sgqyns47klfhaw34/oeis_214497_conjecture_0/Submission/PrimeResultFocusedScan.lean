import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def hasNatPrimeResult (e : Expr) : Bool :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => hasNatPrimeResult b
  | e => e.isAppOf ``Nat.Prime

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    if shown < 250 && hasNatPrimeResult ci.type then
      shown := shown + 1
      logInfo m!"{n} : {ci.type}"
