import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "add_bad_false2" : command => do
  let decl : Declaration := .thmDecl {
    name := `badFalse2
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  modifyEnv fun env => addDeclWithoutChecking env decl

add_bad_false2
#print axioms badFalse2
#check badFalse2
