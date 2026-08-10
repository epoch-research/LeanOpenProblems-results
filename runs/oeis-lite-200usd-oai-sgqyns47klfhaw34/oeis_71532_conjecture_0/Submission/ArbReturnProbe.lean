import FormalConjectures.Util.ProblemImports
#check Lean.Environment.unsafeRunMetaM
#print Lean.Environment.unsafeRunMetaM
#check Function.sometimes
#print Function.sometimes
#check Decidable.byCases
#print Decidable.byCases

-- Try unsafeRunMetaM to produce False? requires Inhabited False, so blocked if sound.
example : False := by
  exact Lean.Environment.unsafeRunMetaM (α := False) (panic! "x") (← getEnv) -- probably syntax/unsafe
