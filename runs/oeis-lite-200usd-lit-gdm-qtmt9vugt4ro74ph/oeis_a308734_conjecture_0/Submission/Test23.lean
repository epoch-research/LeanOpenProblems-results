import FormalConjectures.Util.ProblemImports

open Lean Elab Command Meta

run_meta do
  let env ← getEnv
  let name := `foo
  let val : TheoremVal := {
    name := name
    levelParams := []
    type := mkConst `Nat []
    value := mkNatLit 42
    all := [name]
  }
  let decl := Declaration.thmDecl val
  match unsafe addDeclWithoutCheckingUnsafe env decl with
  | Except.ok env' =>
    setEnv env'
    IO.println "Successfully added foo in run_meta!"
  | Except.error _ => IO.println "Failed to add foo!"

run_meta do
  let env ← getEnv
  if env.contains `foo then
    IO.println "foo IS in the environment after run_meta!"
  else
    IO.println "foo is NOT in the environment after run_meta!"
