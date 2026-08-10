import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "#scan_power" : command => do
  let env ← getEnv
  let mut c := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let t := ci.type
    let s := toString t
    if (s == "False" || s.contains "∀ (P : Prop), P" || s.contains "(P : Prop) → P" || s.contains "Nonempty False" || s.contains "Inhabited False") then
      let axs ← Lean.collectAxioms name
      if !(axs.contains `sorryAx) && c < 500 then
        logInfo m!"{name} : {t} AX {axs}"
        c := c + 1
  logInfo m!"shown {c}"

#scan_power
