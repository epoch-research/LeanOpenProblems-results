import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "#add_self_false" : command => do
  let name := `selfFalseMeta
  let type := mkConst ``False
  let val := mkConst name
  liftCoreM <| addDecl (.thmDecl { name := name, levelParams := [], type := type, value := val })

#add_self_false
#check selfFalseMeta
#print axioms selfFalseMeta

theorem arbitrary (P : Prop) : P := False.elim selfFalseMeta
#print axioms arbitrary
