import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "add_bad" : command => do
  let decl : TheoremVal := { name := `badFalse, levelParams := [], type := mkConst `False, value := mkConst `True.intro }
  liftCoreM <| addDecl (.thmDecl decl)
add_bad
#check badFalse
#print axioms badFalse
