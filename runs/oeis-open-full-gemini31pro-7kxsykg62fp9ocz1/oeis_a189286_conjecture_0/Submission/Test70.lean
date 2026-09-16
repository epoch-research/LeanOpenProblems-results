import Submission.Spec
open Nat Finset

lemma type_of_lemma_disproof : (type_of% @oeis_a189286_conjecture_0) = ∀ (n : ℕ),
  if n = 0 then True else
    have numerator_int : ℤ := ∑ k ∈ Finset.range (n + 1), ↑(T_term k) * ↑(T_term (n - k));
    have denominator : ℤ := (2 * ↑n - 1) * ↑((3 * n).choose n);
    denominator ∣ numerator_int := rfl

theorem disproof_test : ¬ (type_of% @oeis_a189286_conjecture_0) := by
  rw [type_of_lemma_disproof]
  intro h
  have h2 := h 2
  revert h2
  unfold T_term
  norm_num
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
  norm_num
  intro h3
  revert h3
  decide
