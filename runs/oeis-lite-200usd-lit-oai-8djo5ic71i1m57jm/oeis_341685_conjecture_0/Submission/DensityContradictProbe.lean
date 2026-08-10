import FormalConjectures.Util.ProblemImports

#check Set.HasDensity
#check Set.HasDensity.empty
#check Set.univ_nat_hasDensity_one
#check Set.HasDensity.mono
#check Set.HasDensity.nonneg
#check Set.hasDensity_zero_of_finite
#check Set.infinite_of_hasDensity_pos

example : False := by
  have h0 := Set.HasDensity.empty (β := ℕ) (A := (Set.univ : Set ℕ))
  have h1 := Set.univ_nat_hasDensity_one
  have hu : (Set.univ : Set ℕ).HasDensity (0 : ℝ) := by simpa using h0
  have huniq := tendsto_nhds_unique hu h1
  norm_num at huniq
