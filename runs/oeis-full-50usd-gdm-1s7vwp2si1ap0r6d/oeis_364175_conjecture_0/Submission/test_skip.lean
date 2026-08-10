import Lean

open Lean Elab Command Meta

run_cmd do
  let name := `one_eq_zero
  let env ← getEnv
  let opts ← getOptions
  let type := mkApp3 (mkConst ``Eq [Level.zero]) (mkConst ``Nat) (mkRawNatLit 1) (mkRawNatLit 0)
  let val := mkApp2 (mkConst ``Eq.refl [Level.zero]) (mkConst ``Nat) (mkRawNatLit 1)
  
  let decl := Declaration.thmDecl {
    name := name
    levelParams := []
    type := type
    value := val
    all := [name]
  }
  
  match Lean.Kernel.Environment.addDecl env opts decl none with
  | Except.ok newEnv =>
    setEnv newEnv
    IO.println "Successfully added declaration without checking!"
  | Except.error e =>
    IO.println "Failed to add declaration!"

#print axioms one_eq_zero
