import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "add_bad_false" : command => do
  let decl : Declaration := .thmDecl {
    name := `badFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  liftCoreM <| addDecl decl

set_option debug.skipKernelTC true in
add_bad_false

#print axioms badFalse
#check badFalse
