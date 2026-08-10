import FormalConjectures.Util.ProblemImports
import Lean
open Lean Elab Command
elab "addbad" : command => do
  liftCoreM <| addDecl <| Declaration.thmDecl {name := `badthm, levelParams := [], type := mkConst `False, value := mkConst ``True.intro}
addbad
#check badthm
#print axioms badthm
