import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "add_self_target" : command => do
  let decl : Declaration := .thmDecl { name := `foo, levelParams := [], type := .const ``True [], value := .const `foo [] }
  try liftCoreM <| addDecl decl catch e => logWarning m!"caught"
add_self_target
#print axioms foo
#check foo
