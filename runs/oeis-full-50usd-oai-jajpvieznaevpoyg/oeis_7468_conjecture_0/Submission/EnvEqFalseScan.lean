import FormalConjectures.Util.ProblemImports
open Lean Elab Command

elab "#scan_bad_eq" : command => do
  let env ← getEnv
  let trueE := mkConst ``True
  let falseE := mkConst ``False
  let tf := mkApp3 (mkConst ``Eq [levelOne]) (mkSort levelZero) trueE falseE
  let ft := mkApp3 (mkConst ``Eq [levelOne]) (mkSort levelZero) falseE trueE
  let mut found := #[]
  for (n, ci) in env.constants.toList do
    let t := ci.type
    if t == tf || t == ft then found := found.push n
  logInfo m!"found {found.size}: {found.extract 0 (min found.size 100)}"
#scan_bad_eq
