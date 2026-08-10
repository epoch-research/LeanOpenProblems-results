import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command

partial def countConst (n : Name) : Expr → Nat
| .const m _ => if m == n then 1 else 0
| .app f a => countConst n f + countConst n a
| .lam _ t b _ => countConst n t + countConst n b
| .forallE _ t b _ => countConst n t + countConst n b
| .letE _ t v b _ => countConst n t + countConst n v + countConst n b
| .mdata _ b => countConst n b
| .proj _ _ b => countConst n b
| _ => 0

partial def hasExists : Expr → Bool
| .const ``Exists _ => true
| .app f a => hasExists f || hasExists a
| .lam _ t b _ => hasExists t || hasExists b
| .forallE _ t b _ => hasExists t || hasExists b
| .letE _ t v b _ => hasExists t || hasExists v || hasExists b
| .mdata _ b => hasExists b
| .proj _ _ b => hasExists b
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    let c := countConst ``Nat.Prime ci.type
    if c >= 2 && hasExists ci.type then
      logInfo m!"PAIR {name} : {ci.type}"
      found := found + 1
      if found > 300 then break
  logInfo m!"found {found}"
