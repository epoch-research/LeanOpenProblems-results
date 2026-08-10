import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "#add_self_bad" : command => do
  let decl := Declaration.thmDecl { name := `selfBad, levelParams := [], type := .const ``False [], value := .const `selfBad [] }
  addDecl decl

#add_self_bad
#check selfBad
#print axioms selfBad
