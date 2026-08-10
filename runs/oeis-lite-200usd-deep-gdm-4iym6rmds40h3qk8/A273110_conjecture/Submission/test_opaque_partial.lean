import Lean

open Lean Elab Command Term Meta

-- We will add a partial definition `my_partial_val` of type `Inhabited (Nonempty False)`
-- and then a safe opaque constant `my_opaque_val` of type `Nonempty False` using `default`.

#eval (do
  let name1 := `my_partial_val
  let name2_helper := `my_partial_helper
  let type1 ← liftTermElabM do
    let e ← elabTerm (← `(Inhabited (Nonempty False))) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let decl1 : DefinitionVal := {
    name := name1
    levelParams := []
    type := type1
    value := Lean.mkConst name2_helper
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.partial
  }
  let decl2 : DefinitionVal := {
    name := name2_helper
    levelParams := []
    type := type1
    value := Lean.mkConst name1
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.partial
  }
  let decl1 := Declaration.mutualDefnDecl [decl1, decl2]
  let env ← getEnv
  match env.addDeclCore 0 decl1 none true with
  | Except.ok env' => setEnv env'
  | Except.error e => throwError e.toMessageData {}
  : CommandElabM Unit)

-- Now we define `my_opaque_val` of type `Nonempty False` with value `default`
-- using the `Inhabited` instance `my_partial_val`.
#eval (do
  let name2 := `my_opaque_val
  let type2 ← liftTermElabM do
    let e ← elabTerm (← `(Nonempty False)) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let val2 ← liftTermElabM do
    let e ← elabTerm (← `(@Inhabited.default (Nonempty False) my_partial_val)) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let decl2 := Declaration.opaqueDecl {
    name := name2
    levelParams := []
    type := type2
    value := val2
    isUnsafe := false
  }
  let env ← getEnv
  match env.addDeclCore 0 decl2 none true with
  | Except.ok env' => setEnv env'
  | Except.error e => throwError e.toMessageData {}
  : CommandElabM Unit)

-- Now we define a safe theorem `my_theorem` of type `False` with value `Classical.choice my_opaque_val`.
theorem my_theorem : False := Classical.choice my_opaque_val

#print my_theorem
#print axioms my_theorem
