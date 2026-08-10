import Lean

open Lean

initialize
  let name := `my_init_decl
  let type := mkConst `Nat
  let val := mkNatLit 42
  let decl := Declaration.defnDecl {
    name := name
    levelParams := []
    type := type
    value := val
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.safe
  }
  addDecl decl

#check my_init_decl
