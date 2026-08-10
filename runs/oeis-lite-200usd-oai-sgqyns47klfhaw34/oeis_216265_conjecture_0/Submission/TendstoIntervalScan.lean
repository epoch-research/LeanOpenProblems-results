import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let keys := ["Tendsto", "atTop", "Monotone", "StrictMono", "surjective", "unbounded", "Unbounded", "exists_gt", "eventually"]
  for (name, ci) in env.constants.toList do
    let ns := toString name
    let s := toString ci.type
    if (ns.startsWith "Nat." || ns.startsWith "Filter." || ns.startsWith "Function." || ns.startsWith "Set.") &&
       (keys.any fun k => s.contains k || ns.contains k) &&
       (s.contains "ℕ" && (s.contains "∀" || s.contains "∃")) then
      if (s.contains "Tendsto" || s.contains "atTop" || s.contains "Surjective" || s.contains "Monotone") then
        if ns.contains "primeCounting" || ns.contains "count" || (s.contains "Monotone" && s.contains "Tendsto") || (s.contains "Surjective" && s.contains "Monotone") then
          logInfo m!"{name} : {ci.type}"
