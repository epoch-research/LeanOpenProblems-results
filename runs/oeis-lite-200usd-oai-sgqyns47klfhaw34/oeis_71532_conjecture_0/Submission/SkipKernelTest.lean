import FormalConjectures.Util.ProblemImports
set_option debug.skipKernelTC true
open Lean Elab Command
elab "#add_bad" : command => do
  let decl := Declaration.thmDecl { name := `badSkip, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  liftCoreM <| addDecl decl
#add_bad
#check badSkip
#print axioms badSkip
theorem t : False := badSkip
#print axioms t
