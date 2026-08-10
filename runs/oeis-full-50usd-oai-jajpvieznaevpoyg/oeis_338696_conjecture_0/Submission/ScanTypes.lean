import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#scan_type_strings" : command => liftCoreM do
  let env ← getEnv
  let needles := ["octagonal", "polygonal", "3 *", "^ 3", "sqrt"]
  let mut c := 0
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "octagonal" || s.contains "polygonal" || s.contains "Waring" || s.contains "threeSquares" || s.contains "sum_three" then
      logInfo m!"name {n} : {ci.type}"
      c := c+1
  logInfo m!"count {c}"
#scan_type_strings
