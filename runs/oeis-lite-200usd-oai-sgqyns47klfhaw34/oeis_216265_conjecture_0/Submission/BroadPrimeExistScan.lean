import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

partial def constsIn : Expr → NameSet
| .const n _ => NameSet.empty.insert n
| .app f a => (constsIn f).merge (constsIn a)
| .lam _ t b _ | .forallE _ t b _ => (constsIn t).merge (constsIn b)
| .letE _ t v b _ => ((constsIn t).merge (constsIn v)).merge (constsIn b)
| .mdata _ e | .proj _ _ e => constsIn e
| _ => NameSet.empty

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let cs := constsIn ci.type
    if cs.contains `Exists && cs.contains ``Nat.Prime && (cs.contains ``LT.lt || cs.contains ``LE.le) then
      let s := toString ci.type
      -- Require at least two comparison symbols in pretty type.
      let cmp := (s.splitOn "≤").length + (s.splitOn "<").length
      if cmp >= 4 then
        let ns := toString name
        if !(ns.contains "match" || ns.contains "_proof" || ns.contains "._" || ns.contains "inst" || ns.contains "Sylow" || ns.contains "Padic" || ns.contains "Ideal" || ns.contains "ZMod" || ns.contains "Polynomial") then
          count := count + 1
          if count ≤ 300 then logInfo m!"{name} : {ci.type}"
  logInfo m!"total {count}"
