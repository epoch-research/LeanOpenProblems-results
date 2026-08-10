import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.toString.contains "decLoop" then
      logInfo m!"{n} : {ci.type}"
