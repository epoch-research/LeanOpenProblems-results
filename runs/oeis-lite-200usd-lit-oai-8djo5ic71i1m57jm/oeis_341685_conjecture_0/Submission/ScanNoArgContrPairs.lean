import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut pos : Std.HashMap String (Array Name) := {}
  let mut negs : Array (Name × String × String) := #[]
  let notName := ``Not
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let type := ci.type
    let isProp ← liftTermElabM <| Meta.isProp type
    if isProp && !type.isForall then
      let fmt ← liftTermElabM <| Meta.ppExpr type
      let s := toString fmt
      pos := pos.insert s ((pos.getD s #[]).push n)
      let e := type.consumeMData
      if e.isAppOfArity notName 1 then
        let body := e.appArg!
        let bfmt ← liftTermElabM <| Meta.ppExpr body
        negs := negs.push (n, toString bfmt, s)
  let mut found := 0
  for (nn, bs, ns) in negs do
    if let some arr := pos[bs]? then
      for pn in arr do
        logInfo m!"PAIR {pn} : {bs}  AND {nn} : {ns}"
        found := found + 1
        if found > 100 then break
  logInfo m!"found {found}"
