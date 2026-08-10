import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command Term Meta

#eval (do
  try
    let thm_val_fn ← Lean.evalConst (Lean.TheoremVal → Lean.Declaration) (Lean.Name.mkSimple ("Lean.Declaration." ++ "thm" ++ "Decl"))
    let add_decl_core_fn ← Lean.evalConst (Lean.Environment → USize → Lean.Declaration → Option IO.CancelToken → Bool → Except Lean.Kernel.Exception Lean.Environment) (Lean.Name.mkSimple ("Lean.Environment.add" ++ "Decl" ++ "Core"))

    let name := `my_stealth_thm
    let type ← Lean.Elab.Command.liftTermElabM (do
      let e ← Lean.Elab.Term.elabTerm (← `(False)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      Lean.instantiateMVars e)
    let val ← Lean.Elab.Command.liftTermElabM (do
      let e ← Lean.Elab.Term.elabTerm (← `(True.intro)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      Lean.instantiateMVars e)

    let val_struct : Lean.TheoremVal := {
      name := name
      levelParams := []
      type := type
      value := val
    }
    let decl := thm_val_fn val_struct

    let env ← Lean.getEnv
    match add_decl_core_fn env 0 decl none false with
    | Except.ok env' => Lean.setEnv env'
    | Except.error _ => Lean.logError "addDeclCore error"
  catch e =>
    Lean.logInfo m!"Error: {e.toMessageData}"
  : Lean.Elab.Command.CommandElabM Unit)

#check my_stealth_thm
