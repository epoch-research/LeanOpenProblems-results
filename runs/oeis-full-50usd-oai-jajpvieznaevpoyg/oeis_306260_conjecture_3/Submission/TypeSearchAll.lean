import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := ["∀", "Exists", "Nat", "Int"]
  for (n,ci) in env.constants.toList do
    let s := toString n
    if s.contains "Jacobi" || s.contains "jacobi" || s.contains "theta" || s.contains "Theta" || s.contains "local" || s.contains "Local" || s.contains "Quadratic" || s.contains "quadratic" || s.contains "Form" then
      logInfo m!"{n} : {ci.type}"
