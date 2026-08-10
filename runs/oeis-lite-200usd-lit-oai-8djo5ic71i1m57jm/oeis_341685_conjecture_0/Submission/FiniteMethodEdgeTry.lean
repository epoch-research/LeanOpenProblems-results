import FormalConjectures.Util.ProblemImports
open FormalConjecturesForMathlib.Probability
#check Finset.exists_eq_zero_of_sum_lt_card
#check Finset.exists_eq_zero_of_real_sum_lt_card
example : False := by
  have h := Finset.exists_eq_zero_of_sum_lt_card (s := ({0} : Finset ℕ)) (f := fun _ => (1 : ℕ)) (by norm_num)
  rcases h with ⟨x,hx,h0⟩
  norm_num at h0
