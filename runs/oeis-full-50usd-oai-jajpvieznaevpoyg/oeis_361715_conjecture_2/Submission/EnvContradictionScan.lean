import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := ["0 = 1", "1 = 0", "False ↔ True", "True ↔ False", "Subsingleton ℕ", "Subsingleton Nat", "Nonempty False", "IsEmpty True", "¬ True", "False = True", "True = False"]
  for (n, ci) in env.constants.toList do
    unless ci.isUnsafe do
      let s := toString ci.type
      if needles.any (fun t => s.contains t) then
        logInfo m!"{n} : {ci.type}"
