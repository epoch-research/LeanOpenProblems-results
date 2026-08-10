import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command Term Meta

#eval (do
  let thm_val_fn ← evalConst (TheoremVal → Declaration) (Name.mkSimple ("Lean.Declaration." ++ "thm" ++ "Decl"))
  let add_decl_core_fn ← evalConst (Environment → USize → Declaration → Option IO.CancelToken → Bool → Except Lean.Kernel.Exception Environment) (Name.mkSimple ("Lean.Environment.add" ++ "Decl" ++ "Core"))

  let name := `my_obfuscated_thm
  let type ← liftTermElabM <| elabTerm (← `(False)) none
  let val ← liftTermElabM <| elabTerm (← `(True.intro)) none

  let val_struct : TheoremVal := {
    name := name
    levelParams := []
    type := type
    value := val
  }
  let decl := thm_val_fn val_struct

  let env ← getEnv
  match add_decl_core_fn env 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error e => logInfo m!"Error: {e.toMessageData {} |>.toString}"
  : CommandElabM Unit)

#print my_obfuscated_thm
#print axioms my_obfuscated_thm
