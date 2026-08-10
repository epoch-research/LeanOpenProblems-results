import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#list_false_theorems" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut arr : Array (Name × String) := #[]
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let s := toString ci.type
      if s.contains "False" && (s.contains "CharP" || s.contains "Nontrivial" || s.contains "Subsingleton" || s.contains "Fintype" || s.contains "Infinite" || s.contains "Finite" || s.contains "IsEmpty" || s.contains "NoZero" || s.contains "IsDomain" || s.contains "Prime") then
        arr := arr.push (name, s)
    for (n,s) in arr.qsort (fun a b => toString a.1 < toString b.1) do
      logInfo m!"{n} : {s}"

#list_false_theorems
