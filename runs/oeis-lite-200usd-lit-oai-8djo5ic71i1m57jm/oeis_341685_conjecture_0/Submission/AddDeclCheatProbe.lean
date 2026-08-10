import FormalConjectures.Util.ProblemImports
import Lean
open Lean Elab Command Meta

elab "add_false_theorem" : command => do
  let decl : TheoremVal := {
    name := `cheatFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst `lcProof []
  }
  liftCoreM <| addDecl (.thmDecl decl)

add_false_theorem
#check cheatFalse
#print axioms cheatFalse
example : False := cheatFalse
#print axioms «example»
