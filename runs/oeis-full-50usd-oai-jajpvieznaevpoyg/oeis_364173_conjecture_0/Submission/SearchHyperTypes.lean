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
    let ns := toString n
    let ts := toString ci.type
    if (ns.contains "ordinaryHypergeometric" || ns.contains "Pochhammer" || ts.contains "ordinaryHypergeometric" || ts.contains "Pochhammer") && (ts.contains "ModEq" || ts.contains "ZMOD" || ts.contains "factorial" || ts.contains "Prime") then
      if count < 200 then logInfo m!"{n} : {ci.type}"
      count := count + 1
  logInfo m!"count {count}"
