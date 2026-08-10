import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def containsConstName (target : Name) : Expr → Bool
| .const n _ => n == target
| .app f a => containsConstName target f || containsConstName target a
| .lam _ t b _ => containsConstName target t || containsConstName target b
| .forallE _ t b _ => containsConstName target t || containsConstName target b
| .letE _ t v b _ => containsConstName target t || containsConstName target v || containsConstName target b
| .mdata _ e => containsConstName target e
| .proj _ _ e => containsConstName target e
| _ => false

partial def containsAnyConst (targets : List Name) : Expr → Bool
| .const n _ => targets.contains n
| .app f a => containsAnyConst targets f || containsAnyConst targets a
| .lam _ t b _ => containsAnyConst targets t || containsAnyConst targets b
| .forallE _ t b _ => containsAnyConst targets t || containsAnyConst targets b
| .letE _ t v b _ => containsAnyConst targets t || containsAnyConst targets v || containsAnyConst targets b
| .mdata _ e => containsAnyConst targets e
| .proj _ _ e => containsAnyConst targets e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets := [`Exists, ``LE.le, ``LT.lt, ``Membership.mem, ``Set.Mem]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let t := ci.type
    if containsConstName ``Nat.Prime t && containsAnyConst targets t then
      let ns := toString name
      let s := toString t
      if containsConstName `Exists t || s.contains "Set.I" || s.contains "Finset" || s.contains "primeCounting" || s.contains "nth" || s.contains "∀" then
        if !(ns.contains "inst" || ns.contains "dec" || ns.contains "Decidable" || ns.contains "prime_iff") then
          count := count + 1
          if count ≤ 500 then logInfo m!"{name} : {ci.type}"
  logInfo m!"total printed/eligible {count}"
