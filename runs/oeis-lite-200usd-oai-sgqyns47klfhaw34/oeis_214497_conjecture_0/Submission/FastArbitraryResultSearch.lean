import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

/-- Strip forall binders, keeping domain stack. -/
partial def stripForall (e : Expr) (ds : Array Expr := #[]) : Array Expr × Expr :=
  match e with
  | .forallE _ d b _ => stripForall b (ds.push d)
  | _ => (ds, e)

def isBVarResult : Expr → Bool
| .bvar _ => true
| .app (.const ``Nonempty _) (.bvar _) => true
| .app (.const ``Inhabited _) (.bvar _) => true
| .app (.app (.const ``Decidable _) (.bvar _)) _ => true
| _ => false

partial def containsBVarResult : Expr → Bool
| .bvar _ => true
| .app f a => containsBVarResult f || containsBVarResult a
| .mdata _ e => containsBVarResult e
| .proj _ _ e => containsBVarResult e
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut shown := 0
  let mut cand := 0
  let mut safe := 0
  for (name, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let (_, res) := stripForall ci.type
    if isBVarResult res || (res.isAppOf ``Nonempty && containsBVarResult res) || (res.isAppOf ``Inhabited && containsBVarResult res) then
      cand := cand + 1
      let ax ← collectAxioms name
      if ax.all allowedAx then
        safe := safe + 1
        if shown < 300 then
          logInfo m!"{name} : {ci.type} AX {ax.toList}"
          shown := shown + 1
  logInfo m!"cand={cand}, safe={safe}, shown={shown}"
