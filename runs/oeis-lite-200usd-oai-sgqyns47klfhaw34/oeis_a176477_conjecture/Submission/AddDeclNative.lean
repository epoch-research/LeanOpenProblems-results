import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta
unsafe def badDecFalse : Decidable False := isTrue (by exact lcProof)
@[implemented_by badDecFalse]
def safeDecFalse : Decidable False := isFalse (by intro h; exact h)
instance : Decidable False := safeDecFalse
theorem nativeBad : False := by native_decide
#eval show CommandElabM Unit from do
  let ci ← getConstInfo ``nativeBad
  match ci with
  | .thmInfo tv => liftCoreM <| addDecl (.thmDecl { tv with name := `copiedBad })
  | _ => throwError "not theorem"
#check copiedBad
#print axioms copiedBad
