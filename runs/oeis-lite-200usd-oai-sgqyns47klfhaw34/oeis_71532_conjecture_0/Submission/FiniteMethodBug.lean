import FormalConjectures.Util.ProblemImports
open FormalConjecturesForMathlib.Probability
#check Finset.exists_eq_zero_of_real_sum_lt_card
#print axioms Finset.exists_eq_zero_of_real_sum_lt_card
example : False := by
  have h : (∑ x ∈ ({0}:Finset ℕ), ((1:ℕ):ℝ)) < ( ({0}:Finset ℕ).card : ℝ) := by norm_num
  obtain ⟨a,ha,hz⟩ := Finset.exists_eq_zero_of_real_sum_lt_card (s:={0}) (f:=fun _ : ℕ => 1) h
  norm_num at hz
