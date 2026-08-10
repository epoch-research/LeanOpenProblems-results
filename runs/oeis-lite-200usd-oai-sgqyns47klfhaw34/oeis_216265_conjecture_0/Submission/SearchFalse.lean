import FormalConjectures.Util.ProblemImports

open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let type := ci.type
    if type.isConstOf ``False then
      logInfo m!"FALSE DECL {n}"
      count := count + 1
    if type.isAppOfArity ``Nonempty 1 then
      let arg := type.appArg!
      if arg.isConstOf ``False then
        logInfo m!"NONEMPTY FALSE DECL {n}"
        count := count + 1
  logInfo m!"count {count}"

#synth Nonempty False
