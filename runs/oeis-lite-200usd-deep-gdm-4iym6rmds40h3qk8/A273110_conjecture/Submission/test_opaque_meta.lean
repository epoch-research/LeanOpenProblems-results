import Lean

open Lean Elab Command Meta

elab "add_self_opaque" id:ident : command => do
  let name := id.getId
  let type := mkConst ``False
  let decl := Declaration.opaqueDecl {
    name := name
    levelParams := []
    type := type
    value := mkConst name
    isUnsafe := false
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => IO.println "error!"

add_self_opaque my_opaque_false

theorem my_false_theorem : False := my_opaque_false

#print axioms my_false_theorem

