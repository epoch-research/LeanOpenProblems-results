import FormalConjectures.Util.ProblemImports

open Lean Elab Command
elab "add_bad" : command => do
  let cv : ConstantVal := { name := `badThm, levelParams := [], type := .const ``False [] }
  let tv : TheoremVal := { toConstantVal := cv, value := .const ``True.intro [], all := [] }
  liftCoreM <| addDecl (.thmDecl tv)

add_bad
#check badThm
#print axioms badThm
