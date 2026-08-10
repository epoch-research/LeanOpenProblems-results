import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.startsWith "FormalConjectures" || ns.startsWith "Nat." || ns.startsWith "Int.") &&
       (s.contains "False" || s.contains "¬" || s.contains "= False" || s.contains "Nonempty" || s.contains "Subsingleton") then
      count := count + 1
      if count ≤ 500 then logInfo m!"{name} : {ci.type}"
  logInfo m!"total {count}"
