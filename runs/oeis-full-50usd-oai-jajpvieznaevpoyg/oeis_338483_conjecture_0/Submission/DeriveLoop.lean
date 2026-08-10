import FormalConjectures.Util.ProblemImports

inductive LoopP : Prop where
| mk : LoopP → LoopP

deriving instance Inhabited for LoopP

#check (default : LoopP)

theorem loop_bad : False := by
  let rec no : LoopP → False
  | .mk h => no h
  exact no default
#print axioms loop_bad
