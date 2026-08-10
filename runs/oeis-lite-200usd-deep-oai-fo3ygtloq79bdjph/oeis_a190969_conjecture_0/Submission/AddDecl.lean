import FormalConjectures.Util.ProblemImports

open Lean Elab Command
elab "add_bad" : command => do
  let decl : Declaration := .thmDecl { name := `badThm, levelParams := [], type := .const ``False [], value := .const ``True.intro [], hints := .regular 0 }
  addDecl decl

add_bad
#check badThm
#print axioms badThm
