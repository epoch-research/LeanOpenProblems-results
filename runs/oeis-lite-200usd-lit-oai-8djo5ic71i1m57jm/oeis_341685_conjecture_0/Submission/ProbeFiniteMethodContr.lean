import FormalConjectures.Util.ProblemImports
open Finset

example : False := by
  have h := Finset.exists_eq_zero_of_sum_lt_card (s := (∅ : Finset ℕ)) (f := fun _ => (0:ℕ))
  -- likely premise sum < card: 0 < 0 impossible
  fail_if_success exact h (by norm_num)
  sorry
