import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let s := toString n
    if s.contains "364173" || s.contains "supercongru" || s.contains "Jacobsthal" || s.contains "Wolstenholme" || s.contains "Kazandzidis" || s.contains "Dwork" || s.contains "Minton" then
      logInfo m!"NAME {n} : {ci.type}"
      count := count + 1
  logInfo m!"count names={count}"

partial def containsAny (needles : List Name) (e : Expr) : Bool :=
  needles.any (fun n => e.hasConst n)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let needles := [``Real.Gamma, ``Int.ModEq]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if containsAny needles ci.type then
      let ss := toString ci.type
      if ss.contains "Gamma" && (ss.contains "ModEq" || ss.contains "ZMOD" || ss.contains "choose" || ss.contains "range") then
        logInfo m!"TYPE {n} : {ci.type}"
        count := count + 1
        if count > 100 then break
  logInfo m!"count types={count}"
