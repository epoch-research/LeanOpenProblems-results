import FormalConjectures.Util.ProblemImports
open Lean Elab Command Meta
#eval show CommandElabM Unit from do
  let decl : TheoremVal := { name := `selfBad, levelParams := [], type := mkConst ``True, value := mkConst `selfBad }
  liftCoreM <| addDecl (.thmDecl decl)
#check selfBad
#print axioms selfBad
