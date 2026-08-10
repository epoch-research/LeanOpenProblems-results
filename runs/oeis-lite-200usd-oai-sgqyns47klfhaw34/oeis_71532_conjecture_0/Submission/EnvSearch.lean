import FormalConjectures.Util.ProblemImports

open Lean Elab Command Meta

elab "#find_sorry_false" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if count < 200 then
      let type := ci.type
      if type == mkConst ``False then
        logInfo m!"closed False decl: {name}"
        count := count + 1
  logInfo m!"done count={count}"

elab "#find_bad_types" : command => do
  let env ← getEnv
  let targets : Array Expr := #[
    mkConst ``False,
    mkApp (mkConst ``Nonempty [levelZero]) (mkConst ``False),
    mkApp (mkConst ``Subsingleton [levelZero]) (mkConst ``Nat),
    mkApp (mkConst ``Finite [levelZero]) (mkConst ``Nat)
  ]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    for tgt in targets do
      if ci.type == tgt then
        logInfo m!"decl {name} : {ci.type}"
        count := count + 1
  logInfo m!"bad type count={count}"

#find_sorry_false
#find_bad_types
