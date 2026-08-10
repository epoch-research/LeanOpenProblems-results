import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    -- print theorem/axiom names whose type string contains a suspicious fragment
    let s := toString ty
    if s.contains "∀ (P : Prop), P" || s.contains "forall (P : Prop), P" || s.contains "Prop →" then
      IO.println s!"{n} : {ty}"
      count := count + 1
      if count > 200 then return ()
  IO.println s!"count {count}"
