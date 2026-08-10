import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

elab "#scan_bad" : command => do
  let env ← getEnv
  let targets : Array Expr := #[mkConst ``False]
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let type := ci.type.consumeMData
    -- print declarations whose type syntactically contains forall over Prop returning bound var, or exactly False
    let s := toString type
    if type == mkConst ``False || s.contains "∀ {α : Prop}, α" || s.contains "∀ (α : Prop), α" || s.contains "Prop}, ?" then
      logInfo m!"candidate {name} : {type}"

#scan_bad
