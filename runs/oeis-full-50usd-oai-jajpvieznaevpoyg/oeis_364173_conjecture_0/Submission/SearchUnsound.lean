import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command
#eval show CoreM Unit from do
  let env ← getEnv
  let target := (← MetaM.toIO (ctx := {}) (s := {}) <| pure (.const ``False [])) -- no
  let mut cnt := 0
  for (n, ci) in env.constants.toList do
    let t := ci.type
    -- print names containing false?
    if toString n |>.contains "false" then
      if cnt < 100 then IO.println s!"{n} : {t}"
      cnt := cnt + 1
  IO.println s!"names {cnt}"
