import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let keys := ["prime", "Prime"]
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let s := toString n
    if (s.contains "Prime" || s.contains "prime") && (s.contains "add" || s.contains "succ" || s.contains "sub" || s.contains "two" || s.contains "Twin" || s.contains "twin") then
      arr := arr.push (s, toString ci.type)
  for (s,t) in arr.qsort (fun a b => a.1 < b.1) |>.extract 0 (min arr.size 300) do
    logInfo m!"{s} : {t}"
  logInfo m!"count {arr.size}"
