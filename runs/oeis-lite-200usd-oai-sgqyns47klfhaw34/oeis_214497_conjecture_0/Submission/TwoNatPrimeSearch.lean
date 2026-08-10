import FormalConjectures.Util.ProblemImports
open Lean Elab Command
partial def countConst (needle : Name) : Expr → Nat
| .const n _ => if n == needle then 1 else 0
| .app f a => countConst needle f + countConst needle a
| .lam _ t b _ => countConst needle t + countConst needle b
| .forallE _ t b _ => countConst needle t + countConst needle b
| .letE _ t v b _ => countConst needle t + countConst needle v + countConst needle b
| .mdata _ e => countConst needle e
| .proj _ _ e => countConst needle e
| _ => 0
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr : Array (Name × Nat) := #[]
  for (name, ci) in env.constants.toList do
    let c := countConst ``Nat.Prime ci.type
    if c ≥ 2 then arr := arr.push (name,c)
  let sorted := arr.qsort (fun a b => toString a.1 < toString b.1)
  for (name,c) in sorted.extract 0 (min sorted.size 300) do logInfo m!"{name} ({c})"
  logInfo m!"count={sorted.size}"
