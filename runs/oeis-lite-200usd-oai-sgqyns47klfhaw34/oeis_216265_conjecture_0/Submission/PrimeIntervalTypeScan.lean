import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut hits := #[]
  for (name, ci) in env.constants.toList do
    let ns := toString name
    if ns.startsWith "Nat." || ns.startsWith "Chebyshev." || ns.contains "Prime" || ns.contains "prime" || ns.startsWith "Real." then
      let s := toString ci.type
      if s.contains "∃" && s.contains "Nat.Prime" && (s.contains "≤" || s.contains "<") then
        if (s.contains "+" || s.contains "-" || s.contains "*" || s.contains "^" || s.contains "primeCounting" || s.contains "nth") then
          hits := hits.push m!"{name} : {ci.type}"
  logInfo m!"hits {hits.size}"
  for h in hits do logInfo h
