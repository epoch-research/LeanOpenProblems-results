import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

def allowedAx : Name → Bool
| `propext => true
| `Classical.choice => true
| `Quot.sound => true
| _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut props : Std.HashMap String (Array Name) := {}
  let mut negs : Std.HashMap String (Array Name) := {}
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    -- only closed theorem-like constants with no forall binders and type in Prop
    if ci.type.isForall then continue
    let ty ← liftTermElabM <| instantiateMVars ci.type
    let sort ← liftTermElabM <| inferType ty
    -- check type's type is Sort 0, i.e. the constant's type is a proposition
    match sort with
    | .sort .zero =>
      let s := toString ty
      match ty with
      | .app (.const ``Not _) p =>
        let ps := toString p
        negs := negs.insert ps ((negs.getD ps #[]).push name)
      | _ =>
        props := props.insert s ((props.getD s #[]).push name)
      count := count + 1
    | _ => pure ()
  let mut found := 0
  for (s, ns) in props.toList do
    if let some ms := negs.get? s then
      for n in ns do
        for m in ms do
          let axn ← liftTermElabM <| collectAxioms n
          let axm ← liftTermElabM <| collectAxioms m
          if axn.all allowedAx && axm.all allowedAx then
            logInfo m!"PROP_NEG type={s}\n  P: {n} AX {axn.toList}\n  NP: {m} AX {axm.toList}"
            found := found + 1
            if found > 100 then break
        if found > 100 then break
    if found > 100 then break
  logInfo m!"closed prop count {count}, found {found}"
