import FormalConjectures.Util.ProblemImports

open Lean Elab Command

unsafe def addBad : CommandElabM Unit := do
  let type ← liftTermElabM <| Term.elabType (← `(False))
  let val := mkConst ``lcProof []
  liftCoreM <| addDecl (.thmDecl { name := `badAdded, levelParams := [], type := type, value := val })

elab "add_bad" : command => unsafe addBad

add_bad

#print axioms badAdded

example : False := badAdded
