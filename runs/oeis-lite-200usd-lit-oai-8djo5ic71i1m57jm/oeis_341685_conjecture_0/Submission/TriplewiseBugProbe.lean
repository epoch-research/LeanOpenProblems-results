import FormalConjectures.Util.ProblemImports

#check Set.triplewise_of_encard_lt
#check Set.Triplewise.eq
example : False := by
  have h : ({0,1,2} : Set ℕ).encard < 3 := by norm_num
  have ht := Set.triplewise_of_encard_lt (fun _ _ _ : ℕ => False) h
  have hf : False := ht (by simp) (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num)
  exact hf
