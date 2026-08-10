import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def resultType : Expr → Expr
| .forallE _ _ b _ => resultType b
| e => e

partial def mentionsConst (n : Name) : Expr → Bool
| .const m _ => m == n
| .app f a => mentionsConst n f || mentionsConst n a
| .lam _ t b _ => mentionsConst n t || mentionsConst n b
| .forallE _ t b _ => mentionsConst n t || mentionsConst n b
| .letE _ t v b _ => mentionsConst n t || mentionsConst n v || mentionsConst n b
| .mdata _ e => mentionsConst n e
| .proj _ _ e => mentionsConst n e
| _ => false

elab "#allowed_prop_eq_search" : command => do
  liftTermElabM do
    let env ← getEnv
    let mut shown := 0
    for (name, ci) in env.constants.toList do
      if ci.isUnsafe then continue
      let ax ← collectAxioms name
      if ! ax.all allowedAx then continue
      let s := toString ci.type
      if (s.contains "Prop" || s.contains "True" || s.contains "False" || s.contains "Nonempty" || s.contains "Subsingleton" || s.contains "Unique") &&
         (s.contains "=" || s.contains "↔" || s.contains "Nonempty" || s.contains "Subsingleton" || s.contains "False") then
        if shown < 800 then
          logInfo m!"{name} : {ci.type} AX {ax.toList}"
          shown := shown + 1
    logInfo m!"shown={shown}"

#allowed_prop_eq_search
