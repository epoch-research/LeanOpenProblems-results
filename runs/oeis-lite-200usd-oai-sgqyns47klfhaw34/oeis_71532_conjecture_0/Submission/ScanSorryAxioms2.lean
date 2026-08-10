import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let axs ← Lean.collectAxioms n
    if axs.contains `sorryAx then
      arr := arr.push n
  IO.println s!"sorryAx count {arr.size}"
  for n in arr.qsort (fun a b => toString a < toString b) |>.toList.take 200 do
    IO.println n
