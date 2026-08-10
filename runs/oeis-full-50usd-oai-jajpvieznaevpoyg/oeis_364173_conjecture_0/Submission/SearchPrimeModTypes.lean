import FormalConjectures.Util.ProblemImports
open Lean Elab Command
partial def contains (needle : String) (e : Expr) : Bool := (toString e).contains needle
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if (s.contains "Nat.Prime" || s.contains ".Prime") && (s.contains "ZMOD" || s.contains "MOD" || s.contains "Int.ModEq" || s.contains "Nat.ModEq") then
      if count < 300 then logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
