import FormalConjectures.Util.ProblemImports
open Lean Elab Command
partial def finalResult : Expr → Expr
| .forallE _ _ b _ => finalResult b
| e => e
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr : Array (Name × Expr) := #[]
  for (name, ci) in env.constants.toList do
    let r := finalResult ci.type
    if r.isAppOf ``Not then arr := arr.push (name, ci.type)
  let sorted := arr.qsort (fun a b => toString a.1 < toString b.1)
  for (n,t) in sorted.extract 0 (min sorted.size 300) do logInfo m!"{n} : {t}"
  logInfo m!"count={sorted.size}"
