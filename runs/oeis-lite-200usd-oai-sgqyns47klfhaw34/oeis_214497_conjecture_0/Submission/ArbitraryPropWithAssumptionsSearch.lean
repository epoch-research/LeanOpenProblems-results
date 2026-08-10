import FormalConjectures.Util.ProblemImports
open Lean Elab Command

-- Print names/types whose result is a bound variable and whose type mentions decidable/finite/subsingleton/inhabited.
partial def finalResult : Expr → Expr
| .forallE _ _ b _ => finalResult b
| e => e

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let res := finalResult ci.type
    if res.isBVar then
      let s := toString ci.type
      if s.contains "Decidable" || s.contains "Finite" || s.contains "Fintype" || s.contains "Inhabited" || s.contains "Nonempty" || s.contains "Subsingleton" || s.contains "Unique" then
        count := count + 1
        if shown < 300 then
          logInfo m!"{name} : {ci.type}"
          shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
