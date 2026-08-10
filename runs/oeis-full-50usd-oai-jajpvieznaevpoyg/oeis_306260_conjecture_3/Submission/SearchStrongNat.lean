import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n,ci) in env.constants.toList do
    let s := toString n
    let t := toString ci.type
    if (t.contains "∃" || t.contains "Exists") && (t.contains "ℕ" || t.contains "Nat") && (t.contains "^ 2" || t.contains "sq" || t.contains "square" || t.contains "Square") then
      if s.contains "Nat" || s.contains "Int" || s.contains "ZMod" || s.contains "Prime" then
        logInfo m!"{n} : {ci.type}"
