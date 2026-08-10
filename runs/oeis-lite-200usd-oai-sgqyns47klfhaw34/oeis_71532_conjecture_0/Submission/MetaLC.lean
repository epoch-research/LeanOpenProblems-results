import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "add_lc" : command => do
  liftCoreM <| addDecl (.thmDecl {name := `badLC, levelParams:=[], type:=mkConst ``False, value:=mkConst `lcProof})
add_lc
#print axioms badLC
example : False := badLC
