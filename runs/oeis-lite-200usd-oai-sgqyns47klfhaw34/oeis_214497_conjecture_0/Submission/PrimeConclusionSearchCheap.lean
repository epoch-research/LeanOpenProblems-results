import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def finalResult : Expr → Expr
| .forallE _ _ b _ => finalResult b
| e => e

elab "#prime_conclusion_search_cheap" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    let mut total := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let res := finalResult ci.type
      let rs := toString res
      let s := toString ci.type
      if rs.contains "Nat.Prime" || rs.contains "Prime" then
        if s.contains "∀" && (s.contains "→" || s.contains "↔") && (s.contains "Nat" || s.contains "ℕ") then
          total := total + 1
          if shown < 800 then
            logInfo m!"{name} : {ci.type}"
            shown := shown + 1
    logInfo m!"total={total} shown={shown}"

#prime_conclusion_search_cheap
