import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut props : Array (Name × String) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let type := ci.type
    let isProp ← liftTermElabM <| Meta.isProp type
    if isProp && !type.isForall then
      let fmt ← liftTermElabM <| Meta.ppExpr type
      props := props.push (n, toString fmt)
  logInfo m!"no-arg props {props.size}"
  let mut count := 0
  for (n,s) in props do
    if s.startsWith "¬" || s.contains "False" || s.contains "0 = 1" || s.contains "1 = 0" || s.contains "Nat.Prime 1" then
      logInfo m!"{n} : {s}"
      count := count + 1
      if count > 300 then break
