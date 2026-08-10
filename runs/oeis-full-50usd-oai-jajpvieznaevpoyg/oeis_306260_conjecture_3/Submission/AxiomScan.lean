import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := [`FormalConjectures.Util.Attributes.a_test_to_sanity_check_some_definition]
  for n in names do
    if let some ci := env.find? n then logInfo m!"{n} : {ci.type}" else logInfo m!"no {n}"
#check a_test_to_sanity_check_some_definition
#print axioms a_test_to_sanity_check_some_definition
