import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def finalResult : Expr → Expr
| .forallE _ _ b _ => finalResult b
| e => e

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut candidates : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let res := finalResult ci.type
    if res.isConstOf ``False then
      candidates := candidates.push name
  logInfo m!"false conclusion candidates {candidates.size}"
  let mut shown := 0
  for name in candidates do
    if shown ≥ 200 then break
    let ax ← collectAxioms name
    if ax.all allowedAx then
      let some ci := env.find? name | continue
      logInfo m!"{name} : {ci.type} AX {ax.toList}"
      shown := shown + 1
  logInfo m!"shown {shown}"
