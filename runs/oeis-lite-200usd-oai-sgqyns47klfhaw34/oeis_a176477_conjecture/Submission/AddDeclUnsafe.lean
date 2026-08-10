import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta
#eval show CommandElabM Unit from do
  let decl : TheoremVal := { name := `badAdded, levelParams := [], type := mkConst ``False, value := mkConst `lcProof }
  liftCoreM <| addDecl (.thmDecl decl)
#check badAdded
#print axioms badAdded
