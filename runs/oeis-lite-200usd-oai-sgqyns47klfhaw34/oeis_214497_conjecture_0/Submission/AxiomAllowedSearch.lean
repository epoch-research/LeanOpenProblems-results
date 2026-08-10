import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowed : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let s := toString ci.type
    if (s.contains "False" || s.contains "0 = 1" || s.contains "1 = 0" || s.contains "Nonempty" || s.contains "Inhabited") then
      let ax ← (Lean.Meta.getConstInfo name >>= fun _ => collectAxioms name) <|> pure #[]
      if ax.all allowed then
        count := count + 1
        if shown < 300 then
          logInfo m!"{name} : {ci.type} AX {ax.toList}"
          shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
