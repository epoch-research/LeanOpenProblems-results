import Lean

open Lean

initialize
  registerBuiltinAttribute {
    name := `my_attr
    descr := "test"
    add := fun decl stx kind => do
      let name := `my_attr_decl
      let type := mkConst `Nat
      let val := mkNatLit 123
      let decl := Declaration.defnDecl {
        name := name
        levelParams := []
        type := type
        value := val
        hints := ReducibilityHints.opaque
        safety := DefinitionSafety.safe
      }
      addDecl decl
  }

@[my_attr] def dummy : Nat := 0

#check my_attr_decl
