import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command

partial def countNameInExpr (needle : Name) : Expr → Nat
| .const m _ => if m == needle then 1 else 0
| .app f a => countNameInExpr needle f + countNameInExpr needle a
| .lam _ t b _ => countNameInExpr needle t + countNameInExpr needle b
| .forallE _ t b _ => countNameInExpr needle t + countNameInExpr needle b
| .letE _ t v b _ => countNameInExpr needle t + countNameInExpr needle v + countNameInExpr needle b
| .mdata _ b => countNameInExpr needle b
| .proj _ _ b => countNameInExpr needle b
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
  let needles := [``Nat.Prime, ``Prime]
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    let c := needles.foldl (fun acc nd => acc + countNameInExpr nd ci.type) 0
    if c >= 2 && hasExists ci.type then
      let s := toString ci.type
      if s.contains "+ 2" || s.contains "+ 1" || s.contains "mod" || s.contains "Mod" || s.contains "∀" || s.contains "Infinite" then
        logInfo m!"GPAIR {name} : {ci.type}"
        found := found + 1
        if found > 500 then break
  logInfo m!"found {found}"
