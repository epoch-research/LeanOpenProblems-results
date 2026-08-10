import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta

elab "#add_bad_lc2" : command => do
  let type := mkConst ``False
  let val := mkApp (mkConst `lcProof) type
  liftCoreM <| addDecl (.thmDecl { name := `badLC2, levelParams := [], type := type, value := val })

#add_bad_lc2
#check badLC2
#print axioms badLC2

theorem arbitrary2 (P : Prop) : P := False.elim badLC2
#print axioms arbitrary2
