import Submission.Spec
open Nat Finset

theorem eq_A253187 (n : ℕ) : A253187 n =
  ∑ x ∈ range (n + 1), ∑ y ∈ range (n + 1),
    if pentagonal_first x + pentagonal_second y ≤ n then
      count_generalized_decagonal_index (n - (pentagonal_first x + pentagonal_second y))
    else 0 := rfl
