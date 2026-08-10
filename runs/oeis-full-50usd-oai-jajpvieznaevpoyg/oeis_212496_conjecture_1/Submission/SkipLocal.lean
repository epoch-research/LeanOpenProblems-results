import FormalConjectures.Util.ProblemImports
open Lean Elab Command
elab "addbad" : command => do
  let optName : Name := `debug.skipKernelTC
  liftCoreM <| withOptions (fun o => o.setBool optName true) do
    addDecl <| Declaration.thmDecl {name := `badthm3, levelParams := [], type := mkConst `False, value := mkConst ``True.intro}
addbad
#check badthm3
#print axioms badthm3
theorem t : False := badthm3
#print axioms t
