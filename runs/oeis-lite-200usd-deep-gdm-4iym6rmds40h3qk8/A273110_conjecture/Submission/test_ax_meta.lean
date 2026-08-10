import Lean
open Lean Elab Command Meta

elab "add_true_axiom" id:ident ":" type:term : command => do
  let name := id.getId
  let typeExpr ← liftTermElabM do
    let e ← elabTerm type none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let decl := Declaration.axiomDecl {
    name := name
    levelParams := []
    type := typeExpr
    isUnsafe := false
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => pure ()

add_true_axiom my_true_ax : True

#print axioms my_true_ax
