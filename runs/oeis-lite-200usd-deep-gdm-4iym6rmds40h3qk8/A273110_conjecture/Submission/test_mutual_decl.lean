import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command Term Meta

#eval (do
  let name1 := `f_test
  let name2 := `g_test
  let type ← liftTermElabM do
    let e ← elabTerm (← `(False)) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let decl1 : DefinitionVal := {
    name := name1
    levelParams := []
    type := type
    value := Lean.mkConst name2
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.partial
  }
  let decl2 : DefinitionVal := {
    name := name2
    levelParams := []
    type := type
    value := Lean.mkConst name1
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.partial
  }
  let decl := Declaration.mutualDefnDecl [decl1, decl2]
  let env ← getEnv
  match env.addDeclCore 0 decl none true with
  | Except.ok env' => setEnv env'
  | Except.error e => logInfo m!"Error: {e.toMessageData {}}"
  : CommandElabM Unit)

#check f_test
#print f_test
#print axioms f_test
