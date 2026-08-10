import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

partial def containsConstName (needle : Name) : Expr → Bool
| .const n _ => n == needle
| .app f a => containsConstName needle f || containsConstName needle a
| .lam _ t b _ => containsConstName needle t || containsConstName needle b
| .forallE _ t b _ => containsConstName needle t || containsConstName needle b
| .letE _ t v b _ => containsConstName needle t || containsConstName needle v || containsConstName needle b
| .mdata _ e => containsConstName needle e
| .proj _ _ e => containsConstName needle e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut arr := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    let s := toString n
    if containsConstName ``Nat.Prime t &&
       (containsConstName ``LT.lt t || containsConstName ``LE.le t) &&
       (s.startsWith "Nat." || s.startsWith "Chebyshev" || s.contains "prime" || s.contains "Prime") then
      arr := arr.push (n, t)
  arr := arr.qsort (fun a b => toString a.1 < toString b.1)
  let mut count := 0
  for (n,t) in arr do
    if count < 500 then
      logInfo m!"{n} : {t}"
    count := count + 1
  logInfo m!"TOTAL {count}"
