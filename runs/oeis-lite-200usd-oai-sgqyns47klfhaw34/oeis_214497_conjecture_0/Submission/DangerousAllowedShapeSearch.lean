import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

partial def collectForalls : Expr → List (Name × Expr) × Expr
| .forallE n d b _ =>
    let (xs, r) := collectForalls b
    ((n,d)::xs, r)
| e => ([], e)

partial def hasLooseBVar : Expr → Bool
| .bvar _ => true
| .app f a => hasLooseBVar f || hasLooseBVar a
| .lam _ t b _ => hasLooseBVar t || hasLooseBVar b
| .forallE _ t b _ => hasLooseBVar t || hasLooseBVar b
| .letE _ t v b _ => hasLooseBVar t || hasLooseBVar v || hasLooseBVar b
| .mdata _ e => hasLooseBVar e
| .proj _ _ e => hasLooseBVar e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let ax ← collectAxioms name
    if ! ax.all allowedAx then continue
    let (_, res) := collectForalls ci.type
    let s := toString ci.type
    let dangerous :=
      (match res with
       | .bvar _ => true
       | .sort _ => false
       | _ => false) ||
      (hasLooseBVar res && (s.contains "Nonempty" || s.contains "Inhabited" || s.contains "Decidable")) ||
      (s.contains "∀ {α : Prop}, α" || s.contains "∀ (α : Prop), α" || s.contains "∀ {P : Prop}, P" || s.contains "∀ (P : Prop), P")
    if dangerous then
      count := count + 1
      if shown < 500 then
        logInfo m!"{name} : {ci.type} AX {ax.toList}"
        shown := shown + 1
  logInfo m!"count={count}, shown={shown}"
