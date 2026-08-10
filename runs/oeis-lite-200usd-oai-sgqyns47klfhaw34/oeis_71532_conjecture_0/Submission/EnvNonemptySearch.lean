import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command

elab "#search_nonempty_type" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if count < 300 then
      let t := ci.type
      let s := toString t
      if s.contains "Nonempty" || s.contains "∃" then
        if s.contains "[]" || s.contains "inst" || s.contains "class" || s.contains "NoMax" || s.contains "NoMin" || s.contains "SuccOrder" || s.contains "Preorder" || s.contains "LinearOrder" then
          logInfo m!"{name} : {t}"
          count := count + 1

#search_nonempty_type
