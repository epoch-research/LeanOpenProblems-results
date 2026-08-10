import FormalConjectures.Util.ProblemImports
open Lean Meta

unsafe def countConst (n : Name) : Expr → Nat
| .const m _ => if m == n then 1 else 0
| .app f a => countConst n f + countConst n a
| .lam _ t b _ => countConst n t + countConst n b
| .forallE _ t b _ => countConst n t + countConst n b
| .letE _ t v b _ => countConst n t + countConst n v + countConst n b
| .lit _ => 0
| .mdata _ e => countConst n e
| .proj _ _ e => countConst n e
| _ => 0

unsafe def hasLitNat (k : Nat) : Expr → Bool
| .lit (.natVal n) => n == k
| .app f a => hasLitNat k f || hasLitNat k a
| .lam _ t b _ => hasLitNat k t || hasLitNat k b
| .forallE _ t b _ => hasLitNat k t || hasLitNat k b
| .letE _ t v b _ => hasLitNat k t || hasLitNat k v || hasLitNat k b
| .mdata _ e => hasLitNat k e
| .proj _ _ e => hasLitNat k e
| _ => false

unsafe def search23 : CoreM Unit := do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if countConst ``Nat.Prime t > 0 && countConst ``HPow.hPow t > 0 && (hasLitNat 2 t || hasLitNat 3 t) then
      arr := arr.push (n,t)
  logInfo m!"prime pow 2/3 candidates {arr.size}"
  for (n,t) in arr[:arr.size.min 500] do logInfo m!"P23 {n}: {t}"
#eval! search23
