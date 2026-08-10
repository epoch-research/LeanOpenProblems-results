import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    unless ci.isUnsafe do
      let s := toString ci.type
      if (s.contains "ModEq" && s.contains "choose" && s.contains "Prime") ||
         (s.contains "factorization" && s.contains "choose") ||
         (s.contains "multichoose" && s.contains "ModEq") ||
         (s.contains "p ^" && s.contains "ModEq" && s.contains "Prime") then
        logInfo m!"{n} : {ci.type}"
