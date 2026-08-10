import FormalConjectures.Util.ProblemImports
open Lean Meta

unsafe def allowedArr (axs : Array Name) : Bool :=
  axs.all fun n => n == `propext || n == `Classical.choice || n == `Quot.sound

unsafe def modIsFC (env : Environment) (n : Name) : Bool := Id.run do
  let some midx := env.getModuleIdxFor? n | return false
  let mods := env.allImportedModuleNames
  let mname := mods[midx.toNat]!
  return mname.toString.startsWith "FormalConjecturesForMathlib"

#eval show MetaM Unit from do
  let env ← getEnv
  let mut arr : Array (Name × String × String) := #[]
  for (n, ci) in env.constants.toList do
    if modIsFC env n then
      match ci with
      | .thmInfo _ =>
        let axioms ← Lean.collectAxioms n
        if allowedArr axioms then
          let fmt ← ppExpr ci.type
          let some midx := env.getModuleIdxFor? n | pure ()
          let mname := env.allImportedModuleNames[midx.toNat]!.toString
          arr := arr.push (n, mname, fmt.pretty)
      | _ => pure ()
  arr := arr.qsort (fun a b => a.1.toString < b.1.toString)
  for (n,m,t) in arr do
    logInfo m!"[{m}] {n} : {t}"
