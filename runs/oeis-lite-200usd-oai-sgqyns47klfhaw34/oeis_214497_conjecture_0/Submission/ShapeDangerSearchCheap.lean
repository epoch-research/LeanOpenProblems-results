import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def finalResult : Expr → Expr
| .forallE _ _ b _ => finalResult b
| e => e

partial def isDangerResult : Expr → Bool
| .bvar _ => true
| .app (.const ``Nonempty _) (.bvar _) => true
| .app (.const ``Inhabited _) (.bvar _) => true
| .app (.const ``Decidable _) (.bvar _) => true
| _ => false

elab "#shape_danger_search_cheap" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut count := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let r := finalResult ci.type
      if isDangerResult r then
        if count < 300 then logInfo m!"{name} : {ci.type}"
        count := count + 1
    logInfo m!"count={count}"

#shape_danger_search_cheap
