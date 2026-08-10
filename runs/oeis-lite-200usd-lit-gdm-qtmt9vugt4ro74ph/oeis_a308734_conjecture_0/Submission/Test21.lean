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
    setEnv env'
    IO.println "Successfully added foo!"
  | Except.error _ => IO.println "Failed to add foo!"

add_foo

#check foo
