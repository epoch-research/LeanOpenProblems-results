import FormalConjectures.Util.ProblemImports

open Lean Elab Command Meta

unsafe def noForall : Expr → Bool
| .forallE .. => false
| _ => true

unsafe def closedFalseSearch : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t.isConstOf ``False then arr := arr.push n
  logInfo m!"exact closed False constants: {arr.size}"
  for n in arr do logInfo m!"CLOSED_FALSE {n}"

#eval! closedFalseSearch
