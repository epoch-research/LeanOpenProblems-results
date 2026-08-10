import FormalConjectures.Util.ProblemImports

open Lean Elab Command

elab "add_foo" : command => do
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
    liftCoreM (setEnv env')
    IO.println "Successfully added foo!"
  | Except.error _ => IO.println "Failed to add foo!"

add_foo

run_meta do
  let env ← getEnv
  if env.contains `foo then
    IO.println "foo IS in the environment of the next command!"
  else
    IO.println "foo is NOT in the environment of the next command!"
