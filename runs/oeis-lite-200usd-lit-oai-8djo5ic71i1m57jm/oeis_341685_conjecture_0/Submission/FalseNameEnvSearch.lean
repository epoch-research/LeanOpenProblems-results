import FormalConjectures.Util.ProblemImports
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := (toString n).toLower
    if s.contains "false" || s.contains "contrad" || s.contains "inconsistent" then
      count := count + 1
      if count < 500 then IO.println s!"{n} : {ci.type}"
  IO.println s!"count {count}"
