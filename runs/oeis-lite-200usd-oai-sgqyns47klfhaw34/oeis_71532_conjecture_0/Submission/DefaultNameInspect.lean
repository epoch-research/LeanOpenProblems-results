import FormalConjectures.Util.ProblemImports

def g (x : Nat := 3) (y : Nat := 4) := x+y
#check g
#check g._default
#check g._default.1
#check g._default.2
#print g._default.1
#print g._default.2

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  for (n,_) in env.constants.toList do
    if (toString n).contains "g._default" then
      IO.println n
