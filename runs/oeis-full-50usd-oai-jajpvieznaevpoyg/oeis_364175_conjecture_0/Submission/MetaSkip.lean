import FormalConjectures.Util.ProblemImports
set_option debug.skipKernelTC true
open Lean Elab Command
elab "add_bad2" : command => do
  let decl : Declaration := .thmDecl { name := `bad2, levelParams := [], type := .const `False [], value := .const `True.intro [] }
  liftCoreM <| addDecl decl
add_bad2
#check bad2
#print axioms bad2
