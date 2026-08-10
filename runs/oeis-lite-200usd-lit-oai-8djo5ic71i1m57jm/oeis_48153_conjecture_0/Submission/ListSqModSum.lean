import FormalConjectures.Util.ProblemImports
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let mut c := 0
  for (n, _) in env.constants.toList do
    let s := toString n
    if (s.contains "sq" || s.contains "Sq" || s.contains "pow" || s.contains "Pow") &&
       (s.contains "mod" || s.contains "Mod" || s.contains "ZMod") &&
       (s.contains "sum" || s.contains "Sum" || s.contains "range" || s.contains "Range" || s.contains "le" || s.contains "bound") then
      if c < 500 then IO.println s
      c := c + 1
  IO.println s!"count {c}"
