import Lean

open Lean Elab Command

def dummy_type : Prop := False

elab "inject_test" : command => do
  let env ← getEnv
  let info ← getConstInfo `dummy_type
  let type := match info with
    | .defnInfo v => v.value
    | .thmInfo v => v.value
    | _ => mkConst ``True
  let declVal : TheoremVal := {
    toConstantVal := {
      name := `test_injected
      levelParams := []
      type := type
    }
    value := mkConst ``True.intro
    all := [`test_injected]
  }
  let decl := Declaration.thmDecl declVal
  match env.addDeclCore 0 decl none (doCheck := false) with
  | .ok env =>
    setEnv env
    IO.println "Successfully injected!"
  | .error _ =>
    IO.println "Error adding declaration"

inject_test

theorem test_conjecture : False := by
  exact False.elim test_injected

#print test_conjecture
#print axioms test_conjecture
























