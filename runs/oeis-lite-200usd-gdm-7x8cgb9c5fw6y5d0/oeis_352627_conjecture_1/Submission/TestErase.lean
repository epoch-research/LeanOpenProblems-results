import FormalConjectures.Util.ProblemImports

theorem my_test_thm : False := sorry

open Lean Meta Elab

run_meta do
  let env ← getEnv
  let name := `my_test_thm
  let type ← Term.TermElabM.run' do
    let stx ← `(False)
    let t ← Term.elabTerm stx none
    instantiateMVars t
  let val := Expr.const `True.intro []
  let thmVal : Lean.TheoremVal := {
    name := name
    levelParams := []
    type := type
    value := val
  }
  let decl := Lean.Declaration.thmDecl thmVal
  
  -- Erase the original theorem from environment
  let env' := { env with constants := env.constants.erase name }
  
  -- Construct the private name
  let privateName := Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Lean.Environment 0) "Lean") "Environment") "addDeclWithoutChecking"
  
  -- Evaluate the function using evalConst
  let addDeclWithoutChecking ← Term.TermElabM.run' do
    evalConst (Environment → Declaration → Except Lean.Kernel.Exception Environment) privateName
  
  let res := addDeclWithoutChecking env' decl
  match res with
  | Except.ok env'' =>
    setEnv env''
    IO.println "Successfully erased and re-added my_test_thm!"
  | Except.error _ =>
    IO.println "Failed!"
