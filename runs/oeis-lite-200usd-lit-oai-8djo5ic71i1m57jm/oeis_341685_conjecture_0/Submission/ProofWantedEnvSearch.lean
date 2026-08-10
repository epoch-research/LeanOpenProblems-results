import FormalConjectures.Util.ProblemImports
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (toString n).toLower.contains "proof" || (toString n).contains "wanted" || (toString n).contains "chudnovsky" || (toString n).contains "conway_99" then
      count := count + 1
      if count < 300 then IO.println n
  IO.println s!"count {count}"
