import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
#print decLoop
#print axioms decLoop
#check decLoop.eq_def
#check decLoop._unary
#check decLoop.match_1
#check _private.Submission.PartialInspect
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    if (toString n).contains "decLoop" then
      Lean.logInfo m!"{n} : {ci.type}"
