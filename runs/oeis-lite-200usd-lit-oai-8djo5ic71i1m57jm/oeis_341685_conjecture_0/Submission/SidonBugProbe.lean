import FormalConjectures.Util.ProblemImports

#check IsSidon
#check IsSidon.insert
#check IsSidon.insert_ge_max'
#check IsSidon.exists_insert

example : False := by
  have hA : IsSidon ((∅ : Set ℕ)) := by simp [IsSidon]
  have h := (IsSidon.insert (A := (∅ : Set ℕ)) (m := 0) hA)
  -- inserted empty is {0}, should be Sidon, RHS true because m∈A false and forall vacuous true
  norm_num at h

example : False := by
  have hA : IsSidon (({0} : Set ℕ)) := by simp [IsSidon]
  have h := (IsSidon.insert (A := ({0} : Set ℕ)) (m := 1) hA)
  -- {0,1} should be Sidon
  norm_num at h
