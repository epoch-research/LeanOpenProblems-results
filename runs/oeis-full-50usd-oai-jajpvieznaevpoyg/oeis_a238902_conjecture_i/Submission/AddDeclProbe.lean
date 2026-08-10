import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta

elab "add_bad" : command => do
  let decl : Declaration := .thmDecl {
    name := `badmeta
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  liftCoreM <| addDecl decl

add_bad
#check badmeta
#print axioms badmeta
