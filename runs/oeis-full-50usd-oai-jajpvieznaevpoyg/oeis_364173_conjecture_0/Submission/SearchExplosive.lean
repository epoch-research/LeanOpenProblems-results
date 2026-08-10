import FormalConjectures.Util.ProblemImports
open Lean Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    let s := toString ci.type
    if s.contains "∀ (P : Prop), P" || s.contains "Nonempty False" || s.contains "False →" || s.contains "False" then
      if cnt < 200 then IO.println s!"{n} : {ci.type}"
      cnt := cnt+1
  IO.println s!"count {cnt}"
