import FormalConjectures.Util.ProblemImports

example : False := by
  have h1 : Powerfree 3 (4 : ℕ) := by
    -- if squarefree/powerfree? 4 is cube-free true
    rw [Powerfree]
    intro r hr
    -- no proof manually
    sorry
  have h2 : Powerfree 2 (4 : ℕ) := Powerfree.of_le (by norm_num : 2 ≤ 3) h1
  rw [powerfree_two] at h2
  norm_num [Squarefree] at h2
