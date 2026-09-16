import Submission.Spec
open Nat Finset

lemma T_term_0 : T_term 0 = 1 := rfl
lemma T_term_1 : T_term 1 = 60 := rfl

lemma type_of_lemma3 : (type_of% @oeis_a189286_conjecture_0) = ∀ (n : ℕ),
  if n = 0 then True else
    have numerator_int : ℤ := ∑ k ∈ Finset.range (n + 1), ↑(T_term k) * ↑(T_term (n - k));
    have denominator : ℤ := (2 * ↑n - 1) * ↑((3 * n).choose n);
    denominator ∣ numerator_int := rfl

theorem disproof_test2 : ¬ (type_of% @oeis_a189286_conjecture_0) := by
  rw [type_of_lemma3]
  intro h
  have h1 := h 1
  revert h1
  norm_num
  rw [sum_range_succ, sum_range_succ, sum_range_zero]
  simp [T_term_0, T_term_1]
