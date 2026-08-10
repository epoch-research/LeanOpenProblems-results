import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def mentions (needle : Name) : Expr → Bool
| .const n _ => n == needle
| .app f a => mentions needle f || mentions needle a
| .lam _ t b _ => mentions needle t || mentions needle b
| .forallE _ t b _ => mentions needle t || mentions needle b
| .letE _ t v b _ => mentions needle t || mentions needle v || mentions needle b
| .mdata _ e => mentions needle e
| .proj _ _ e => mentions needle e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let s := toString ci.type
    if ((s.contains "∀ {α : Prop}, α") ||
        (s.contains "∀ (α : Prop), α") ||
        (s.contains "Nonempty α") ||
        (s.contains "Inhabited α") ||
        (s.contains "∃ x, p x") ||
        (s.contains "∀ (p : ℕ → Prop), ∃") ||
        (mentions ``Nonempty ci.type && s.contains "Prop") ||
        (mentions ``Exists ci.type && s.contains "Nat" && s.contains "Prime")) then
      let ax ← collectAxioms name
      if ax.all allowedAx then
        count := count + 1
        if shown < 300 then
          logInfo m!"{name} : {ci.type} AX {ax.toList}"
          shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
