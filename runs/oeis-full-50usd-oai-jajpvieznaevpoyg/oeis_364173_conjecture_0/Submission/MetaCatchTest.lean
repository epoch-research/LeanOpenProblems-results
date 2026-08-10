import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "add_bad_catch" : command => do
  let decl : Declaration := .thmDecl { name := `badcatch, levelParams := [], type := .const ``False [], value := .const `badcatch [] }
  try
    liftCoreM <| addDecl decl
  catch e =>
    logWarning m!"caught {← e.toMessageData.toString}"
add_bad_catch
#print axioms badcatch
example : False := badcatch
