import FormalConjectures.Util.ProblemImports
open Lean Elab Command

partial def mentionsBVar0 : Expr → Bool
| .bvar 0 => true
| .app f a => mentionsBVar0 f || mentionsBVar0 a
| .lam _ d b _ => mentionsBVar0 d || mentionsBVar0 b
| .forallE _ d b _ => mentionsBVar0 d || mentionsBVar0 b
| .letE _ t v b _ => mentionsBVar0 t || mentionsBVar0 v || mentionsBVar0 b
| .mdata _ e => mentionsBVar0 e
| .proj _ _ e => mentionsBVar0 e
| _ => false

-- after stripping foralls, find declarations with a Prop parameter whose conclusion mentions it positively/at all
partial def suspicious (depth : Nat) : Expr → Bool
| .forallE _ (.sort .zero) b _ =>
    let concl := stripForall b
    mentionsBVar0 concl || suspicious (depth+1) b
| .forallE _ _ b _ => suspicious (depth+1) b
| _ => false
where stripForall : Expr → Expr
| .forallE _ _ b _ => stripForall b
| e => e

elab "#suspicious_scan" : command => do
  let env ← getEnv
  let mut c := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let nstr := toString name
    if nstr.startsWith "Lean." || nstr.startsWith "Mathlib.Tactic" || nstr.startsWith "Aesop" then continue
    if suspicious 0 ci.type then
      if c < 400 then logInfo m!"{name} : {ci.type}"
      c := c + 1
  logInfo m!"count {c}"

#suspicious_scan
