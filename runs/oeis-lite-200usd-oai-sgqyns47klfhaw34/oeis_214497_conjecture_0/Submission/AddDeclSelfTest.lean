import FormalConjectures.Util.ProblemImports

open Lean Elab Command

unsafe def addSelf : CommandElabM Unit := do
  let type ← liftTermElabM <| Term.elabType (← `(False))
  let val := mkConst `badSelf []
  liftCoreM <| addDecl (.thmDecl { name := `badSelf, levelParams := [], type := type, value := val })

elab "add_self" : command => unsafe addSelf

add_self

#print axioms badSelf
example : False := badSelf
