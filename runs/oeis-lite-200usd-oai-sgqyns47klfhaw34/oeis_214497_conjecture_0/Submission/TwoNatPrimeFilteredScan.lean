import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command
partial def countNatPrime (e : Expr) : Nat :=
  let here := if e.isAppOf ``Nat.Prime then 1 else 0
  match e with
  | Expr.app f a => here + countNatPrime f + countNatPrime a
  | Expr.lam _ t b _ => here + countNatPrime t + countNatPrime b
  | Expr.forallE _ t b _ => here + countNatPrime t + countNatPrime b
  | Expr.letE _ t v b _ => here + countNatPrime t + countNatPrime v + countNatPrime b
  | Expr.mdata _ b => here + countNatPrime b
  | Expr.proj _ _ b => here + countNatPrime b
  | _ => here
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  for (n, ci) in env.constants.toList do
    let c := countNatPrime ci.type
    if c ≥ 2 then
      let s := toString ci.type
      if shown < 100 && (s.contains "+ 2" || s.contains "- 2" || s.contains "∃" && s.contains "∧") then
        shown := shown + 1
        logInfo m!"{n} ({c}) : {ci.type}"
  logInfo m!"shown {shown}"
