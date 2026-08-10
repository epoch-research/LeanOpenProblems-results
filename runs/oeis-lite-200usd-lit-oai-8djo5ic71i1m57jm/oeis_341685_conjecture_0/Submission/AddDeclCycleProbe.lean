import FormalConjectures.Util.ProblemImports
import Lean
open Lean Elab Command Meta

elab "add_cycle_theorem" : command => do
  let decl : TheoremVal := {
    name := `cycleFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst `cycleFalse []
  }
  liftCoreM <| addDecl (.thmDecl decl)

add_cycle_theorem
#check cycleFalse
#print axioms cycleFalse
example : False := cycleFalse
#print axioms «example»
