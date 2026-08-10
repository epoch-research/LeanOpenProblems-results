import FormalConjectures.Util.ProblemImports
open Filter Set

#check Nat.hasDensity_even
#check Set.HasDensity.empty
#check tendsto_nhds_unique
#print axioms Nat.hasDensity_even

-- Try compare density of empty and univ only gives different sets.
-- Check if even set also has density 0 from finite theorem? no, infinite.
example : False := by
  have h := Nat.hasDensity_even
  -- if can prove even set finite, false impossible
  norm_num
