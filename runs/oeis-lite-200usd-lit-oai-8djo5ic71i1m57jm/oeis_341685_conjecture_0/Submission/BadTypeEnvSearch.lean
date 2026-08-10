import FormalConjectures.Util.ProblemImports
open Lean Meta
#eval show MetaM Unit from do
  let env ← getEnv
  let propSort := mkSort levelZero
  let arbitraryPropType := mkForall `P BinderInfo.default propSort (mkBVar 0)
  let nonemptyFalse := mkApp (mkConst ``Nonempty [levelZero]) (mkConst ``False)
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if ci.type == arbitraryPropType || ci.type == nonemptyFalse then
      count := count + 1
      IO.println s!"BAD {n} : {ci.type}"
  IO.println s!"count {count}"
