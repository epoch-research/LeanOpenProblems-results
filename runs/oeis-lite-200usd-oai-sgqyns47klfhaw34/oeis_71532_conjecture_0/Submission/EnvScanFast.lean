import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command

def isForallPropReturnsVar (e : Expr) : Bool :=
  match e with
  | .forallE _ (.sort .zero) body _ =>
      match body with
      | .bvar 0 => true
      | .forallE _ (.sort .zero) body2 _ => body2 == .bvar 0 || body2 == .bvar 1
      | _ => false
  | _ => false

elab "#scan_fast" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let type := ci.type.consumeMData
    if type == mkConst ``False || isForallPropReturnsVar type then
      count := count + 1
      logInfo m!"candidate {name} : {type}"
      if count > 100 then break
  logInfo m!"count shown {count}"

#scan_fast
