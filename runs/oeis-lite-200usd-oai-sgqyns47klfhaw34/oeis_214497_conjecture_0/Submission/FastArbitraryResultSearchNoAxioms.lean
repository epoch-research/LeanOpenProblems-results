import FormalConjectures.Util.ProblemImports
open Lean Elab Command
partial def stripForall (e : Expr) : Expr := match e with | .forallE _ _ b _ => stripForall b | _ => e
def isInteresting : Expr → Bool
| .bvar _ => true
| .app (.const ``Nonempty _) (.bvar _) => true
| .app (.const ``Inhabited _) (.bvar _) => true
| _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let res := stripForall ci.type
    if isInteresting res then
      count := count + 1
      if shown < 200 then
        logInfo m!"{name} : {ci.type}"
        shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
