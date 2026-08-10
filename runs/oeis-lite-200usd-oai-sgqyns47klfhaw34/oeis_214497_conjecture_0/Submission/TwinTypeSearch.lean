import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def mentions (needle : Name) : Expr → Bool
| .const n _ => n == needle
| .app f a => mentions needle f || mentions needle a
| .lam _ t b _ => mentions needle t || mentions needle b
| .forallE _ t b _ => mentions needle t || mentions needle b
| .letE _ t v b _ => mentions needle t || mentions needle v || mentions needle b
| .mdata _ e => mentions needle e
| .proj _ _ e => mentions needle e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if mentions ``Nat.Prime ci.type then
      let s := toString ci.type
      let lname := toString name
      if ((s.contains " + 2" || s.contains "+ 2" || s.contains "- 2" || s.contains " - 2" || s.contains "primeGap" || s.contains "nth Nat.Prime" || lname.contains "twin" || lname.contains "Twin" || lname.contains "gap" || lname.contains "Gap") && (s.contains "∃" || s.contains "Infinite" || s.contains "∀")) then
        count := count + 1
        if shown < 200 then
          logInfo m!"{name} : {ci.type}"
          shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
