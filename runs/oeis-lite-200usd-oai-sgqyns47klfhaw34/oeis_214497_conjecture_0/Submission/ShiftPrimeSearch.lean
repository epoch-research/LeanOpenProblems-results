import FormalConjectures.Util.ProblemImports
open Lean Meta

unsafe def countConst (n : Name) : Expr → Nat
| .const m _ => if m == n then 1 else 0
| .app f a => countConst n f + countConst n a
| .lam _ t b _ => countConst n t + countConst n b
| .forallE _ t b _ => countConst n t + countConst n b
| .letE _ t v b _ => countConst n t + countConst n v + countConst n b
| .mdata _ e => countConst n e
| .proj _ _ e => countConst n e
| _ => 0

unsafe def hasConst (n : Name) : Expr → Bool := fun e => countConst n e > 0

unsafe def search : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if countConst ``Nat.Prime t >= 1 && hasConst ``HAdd.hAdd t && hasConst ``HSub.hSub t then
      arr := arr.push (n,t)
  logInfo m!"shift prime candidates {arr.size}"
  for (n,t) in arr[:arr.size.min 300] do logInfo m!"SHIFT {n}: {t}"
#eval! search
