import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "#scan_power_fast" : command => do
  let env ← getEnv
  let mut c := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let s := toString ci.type
    if (s == "False" || s.contains "∀ (P : Prop), P" || s.contains "(P : Prop) → P" || s.contains "Nonempty False" || s.contains "Inhabited False") then
      if c < 300 then logInfo m!"{name} : {ci.type}"
      c := c + 1
  logInfo m!"shown/count {c}"

#scan_power_fast
