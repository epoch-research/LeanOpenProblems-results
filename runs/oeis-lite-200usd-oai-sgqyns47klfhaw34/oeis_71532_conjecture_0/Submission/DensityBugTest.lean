import FormalConjectures.Util.ProblemImports
open Set Filter

#check Set.HasDensity.univ
#check Set.HasDensity.empty
#check Nat.hasDensity_even
#check Nat.infinite_of_hasDensity_pos

-- Try forcing empty infinite via density uniqueness? should fail because hα for 0 absent.
example : False := by
  have h0 : Set.HasDensity (∅ : Set ℕ) 0 := Set.HasDensity.empty
  have h1 : Set.HasDensity ((Set.univ : Set ℕ)) 1 := Set.HasDensity.univ_nat_hasDensity_one
  -- no contradiction
  norm_num

#print axioms Nat.hasDensity_even
