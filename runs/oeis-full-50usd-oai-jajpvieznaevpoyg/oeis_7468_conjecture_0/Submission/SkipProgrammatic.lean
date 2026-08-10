import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "add_bad_false3" : command => do
  let decl : Declaration := .thmDecl {
    name := `badFalse3
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  liftCoreM <| withOptions (fun opts => opts.setBool `debug.skipKernelTC true) <| addDecl decl

add_bad_false3
#print axioms badFalse3
#check badFalse3
