import Lean

open Lean Elab Command Meta

elab "add_self_thm" id:ident : command => do
  let name := id.getId
  let type := mkConst ``False
  let decl := Declaration.thmDecl {
    name := name
    levelParams := []
    type := type
    value := mkConst name
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => IO.println "error!"

add_self_thm my_self_theorem

#print my_self_theorem
#print axioms my_self_theorem
