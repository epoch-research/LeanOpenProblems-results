import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    unless ci.isUnsafe do
      let s := toString ci.type
      if s.contains "Int.ModEq" && (s.contains "3 *" || s.contains "Nat.Prime" || s.contains "^ (3" || s.contains "ZMOD") then
        count := count + 1
        if count < 200 then logInfo m!"{n} : {ci.type}"
  logInfo m!"count {count}"
