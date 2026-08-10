import FormalConjectures.Util.ProblemImports
import Lean
set_option debug.skipKernelTC true
open Lean Elab Command
elab "addbad" : command => do
  liftCoreM <| addDecl <| Declaration.thmDecl {name := `badthm2, levelParams := [], type := mkConst `False, value := mkConst ``True.intro}
addbad
#check badthm2
#print axioms badthm2
theorem t : False := badthm2
#print axioms t
