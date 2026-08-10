import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta

elab "#add_bad_lc" : command => do
  let type := mkConst ``False
  let stx ← `(term| lcProof)
  let val ← runTermElabM fun _ => do Term.elabTerm stx (some type)
  liftCoreM <| addDecl (.thmDecl { name := `badLC, levelParams := [], type := type, value := val })

#add_bad_lc
#check badLC
#print axioms badLC

theorem arbitrary (P : Prop) : P := False.elim badLC
#print axioms arbitrary
