import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command Meta

partial def containsNatPrime : Expr → Bool
| .const ``Nat.Prime _ => true
| .app f a => containsNatPrime f || containsNatPrime a
| .lam _ t b _ => containsNatPrime t || containsNatPrime b
| .forallE _ t b _ => containsNatPrime t || containsNatPrime b
| .letE _ t v b _ => containsNatPrime t || containsNatPrime v || containsNatPrime b
| .mdata _ b => containsNatPrime b
| .proj _ _ b => containsNatPrime b
| _ => false

partial def containsPow3or2 : Expr → Bool
| .app (.app (.app (.const ``HPow.hPow _) _) (.app (.app (.app (.const ``OfNat.ofNat _) _) _) _)) _) _ => true
| .app f a => containsPow3or2 f || containsPow3or2 a
| .lam _ t b _ => containsPow3or2 t || containsPow3or2 b
| .forallE _ t b _ => containsPow3or2 t || containsPow3or2 b
| .letE _ t v b _ => containsPow3or2 t || containsPow3or2 v || containsPow3or2 b
| .mdata _ b => containsPow3or2 b
| .proj _ _ b => containsPow3or2 b
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    if containsNatPrime ci.type then
      let s := toString name
      if s.contains "214497" || s.contains "oeis" || s.contains "OEIS" then
        logInfo m!"NAME {name} : {ci.type}"
        found := found + 1
  logInfo m!"found {found}"
