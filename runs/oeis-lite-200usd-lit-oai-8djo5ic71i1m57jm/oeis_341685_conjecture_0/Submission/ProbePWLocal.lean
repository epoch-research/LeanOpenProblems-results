import FormalConjectures.Util.ProblemImports
proof_wanted mybad : False
#check mybad
#check «mybad»
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← Lean.Elab.Command.getEnv
  for (n, _) in env.constants.toList do
    if (toString n).contains "mybad" then Lean.logInfo m!"{n}"
