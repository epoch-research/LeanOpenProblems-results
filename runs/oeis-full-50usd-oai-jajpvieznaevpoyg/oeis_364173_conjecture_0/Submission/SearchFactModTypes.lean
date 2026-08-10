import FormalConjectures.Util.ProblemImports
open Lean Elab Command
partial def hasConst (nm : Name) : Expr → Bool
| .const n _ => n == nm
| .app f a => hasConst nm f || hasConst nm a
| .lam _ t b _ => hasConst nm t || hasConst nm b
| .forallE _ t b _ => hasConst nm t || hasConst nm b
| .letE _ t v b _ => hasConst nm t || hasConst nm v || hasConst nm b
| .mdata _ e => hasConst nm e
| .proj _ _ e => hasConst nm e
| _ => false
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let ty := ci.type
    if (hasConst ``Int.ModEq ty || hasConst ``Nat.ModEq ty) && (hasConst ``Nat.factorial ty || hasConst ``Nat.choose ty || hasConst ``padicValNat ty) then
      if count < 500 then logInfo m!"{n} : {ty}"
      count := count + 1
  logInfo m!"count {count}"
