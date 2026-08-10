import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command

#eval (do
  let name := `my_eval_thm
  let type ← liftTermElabM <| elabTerm (← `(False)) none
  let decl := Declaration.thmDecl {
    name := name
    levelParams := []
    type := type
    value := ← liftTermElabM <| elabTerm (← `(True.intro)) none
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => pure ()
  : CommandElabM Unit)

#print my_eval_thm
#print axioms my_eval_thm
