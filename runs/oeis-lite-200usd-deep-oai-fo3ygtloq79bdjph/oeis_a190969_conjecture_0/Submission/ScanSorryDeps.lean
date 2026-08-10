import FormalConjectures.Util.ProblemImports

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci.value? with
    | some v =>
      if v.hasConst ``sorryAx then
        IO.println s!"{n} : {ci.type}"
        count := count + 1
        if count > 200 then break
    | none => pure ()
  IO.println s!"count shown {count}"
