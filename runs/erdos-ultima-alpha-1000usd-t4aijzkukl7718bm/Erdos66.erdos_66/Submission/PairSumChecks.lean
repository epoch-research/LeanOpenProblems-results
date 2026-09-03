import Submission.PrefixBalancedCostCompactnessExplore
open scoped Classical
set_option pp.all true in
#print Finset.sum_product
set_option pp.all true in
#check Finset.product
example {β : Type*} [Fintype β] (s : Finset ℕ) (f : ℕ × β → ℝ) :
  (∑ z∈s.product Finset.univ, f z) = ∑ j∈s, ∑ b, f (j,b) := by
  exact Finset.sum_product s Finset.univ f
