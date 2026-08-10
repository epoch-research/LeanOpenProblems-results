import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "add_bad" : command => do
  let decl : Declaration := .thmDecl {
    name := `badMeta
    levelParams := []
    type := .const `False []
    value := .const `badMeta []
  }
  liftCoreM <| addDecl decl

add_bad
#check badMeta
#print axioms badMeta
