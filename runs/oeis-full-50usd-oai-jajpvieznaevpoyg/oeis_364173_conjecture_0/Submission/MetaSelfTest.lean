import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "add_bad" : command => do
  let decl : Declaration := .thmDecl {
    name := `bad
    levelParams := []
    type := .const ``False []
    value := .const `bad []
  }
  liftCoreM <| addDecl decl
add_bad
#print axioms bad
#check bad
example : False := bad
