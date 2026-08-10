import FormalConjectures.Util.ProblemImports

open Lean Elab Command

elab "add_bad" : command => do
  let decl : Declaration := .thmDecl {
    name := `badAdded
    levelParams := []
    type := .const `False []
    value := .const `True.intro []
  }
  liftCoreM <| addDecl decl

add_bad
#check badAdded
#print axioms badAdded
