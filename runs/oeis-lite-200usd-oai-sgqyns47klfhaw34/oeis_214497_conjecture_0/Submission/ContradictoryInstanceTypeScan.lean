import FormalConjectures.Util.ProblemImports
import Lean

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found := 0
  let mut checked := 0
  for (name, ci) in env.constants.toList do
    if name.isInternal || name.hasMacroScopes || ci.isUnsafe then continue
    -- only closed inductive/structure/abbrev constants with type Sort/Type after whnf
    match ci.type with
    | .sort _ => pure ()
    | _ => continue
    checked := checked + 1
    if checked > 5000 then break
    let T := mkConst name
    try
      liftTermElabM do
        discard <| synthInstance (← mkAppM ``Finite #[T])
        discard <| synthInstance (← mkAppM ``Infinite #[T])
      logInfo m!"FINITE_AND_INFINITE {name} : {ci.type}"
      found := found + 1
    catch _ => pure ()
    try
      liftTermElabM do
        discard <| synthInstance (← mkAppM ``Subsingleton #[T])
        discard <| synthInstance (← mkAppM ``Nontrivial #[T])
      logInfo m!"SUBSINGLETON_AND_NONTRIVIAL {name} : {ci.type}"
      found := found + 1
    catch _ => pure ()
  logInfo m!"checked {checked}, found {found}"
