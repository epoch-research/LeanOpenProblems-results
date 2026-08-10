import FormalConjectures.Util.ProblemImports

open Lean Elab Command

elab "add_bad" : command => do
  let val : Declaration := .thmDecl {
    name := `badMeta
    levelParams := []
    type := .const `False []
    value := .const `True.intro []
  }
  liftCoreM <| addDecl val

add_bad
#check badMeta
#print axioms badMeta
example : False := badMeta
