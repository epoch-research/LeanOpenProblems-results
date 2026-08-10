import FormalConjectures.Util.ProblemImports
import Lean
open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := [``Nonempty, ``Inhabited, ``Subsingleton, ``Unique, ``IsEmpty]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let s := toString ci.type
    if (s.contains "∀ (α : Sort" && (s.contains "Nonempty α" || s.contains "Inhabited α" || s.contains "Subsingleton α" || s.contains "Unique α" || s.contains "IsEmpty α")) ||
       (s.contains "∀ {α : Sort" && (s.contains "Nonempty α" || s.contains "Inhabited α" || s.contains "Subsingleton α" || s.contains "Unique α" || s.contains "IsEmpty α")) then
      let axs ← collectAxioms n
      logInfo m!"STRONG {n} : {ci.type} axioms {axs.toList}"
      count := count + 1
      if count > 200 then break
  logInfo m!"done {count}"
