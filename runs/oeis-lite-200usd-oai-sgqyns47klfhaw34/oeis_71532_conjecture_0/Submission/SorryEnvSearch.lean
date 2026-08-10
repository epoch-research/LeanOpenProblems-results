import FormalConjectures.Util.ProblemImports

open Lean Elab Command

elab "#find_sorry_decls" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    let s := toString name
    if count < 500 && (s.contains "Test" || s.contains "test" || s.contains "flagged" || s.contains "what" || s.contains "FormalConjectures") then
      let axs ← Lean.collectAxioms name
      if axs.contains `sorryAx then
        logInfo m!"sorry decl {name} : {ci.type}"
        count := count + 1
  logInfo m!"total shown {count}"

#find_sorry_decls
