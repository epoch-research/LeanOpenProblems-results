import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let pats := ["super", "congru", "wolsten", "jacob", "hypergeom", "gamma", "padic"]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString n
    if pats.any (fun p => s.toLower.contains p) then
      if count < 500 then IO.println s
      count := count+1
  IO.println s!"count {count}"
