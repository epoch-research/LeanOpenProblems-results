import FormalConjectures.Util.ProblemImports
open Set
-- Try theorem concrete consequences that may be false; each example should fail if theorem sound.
example : False := by
  have h := Combinatorics.hypergraphRamsey_self 0
  -- R_0(0)=0 likely ok
  norm_num at h
example : False := by
  have h := iteratedLog_two
  have h0 := Real.iteratedLog_eq_zero_of_le (x := 2) (by norm_num : (2:ℝ) ≤ 1)
  exact (by norm_num at h0)
