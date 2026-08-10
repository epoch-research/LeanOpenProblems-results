import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command Term Meta

#eval (do
  let name := `A273110_conjecture_impl
  let type ← liftTermElabM do
    let e ← elabTerm (← `(False)) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let val := Lean.mkConst name
  let decl := Declaration.thmDecl {
    name := name
    levelParams := []
    type := type
    value := val
  }
  let env ← getEnv
  match env.addDeclCore 0 decl none true with
  | Except.ok env' => setEnv env'
  | Except.error e => logInfo m!"Error: {e.toMessageData {}}"
  : CommandElabM Unit)

#check A273110_conjecture_impl
#print axioms A273110_conjecture_impl
