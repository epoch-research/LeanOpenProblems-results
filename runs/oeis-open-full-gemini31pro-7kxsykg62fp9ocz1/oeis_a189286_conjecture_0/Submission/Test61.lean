import Submission.Spec
open Nat Finset

lemma type_of_lemma_disproof : (type_of% @oeis_a189286_conjecture_0) = ∀ (n : ℕ),
  if n = 0 then True else
    have numerator_int : ℤ := ∑ k ∈ Finset.range (n + 1), ↑(T_term k) * ↑(T_term (n - k));
    have denominator : ℤ := (2 * ↑n - 1) * ↑((3 * n).choose n);
    denominator ∣ numerator_int := rfl

theorem oeis_a189286_conjecture_0_test : type_of% @oeis_a189286_conjecture_0 := by
  rw [type_of_lemma_disproof]
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    have h : (2*n - 1) * (3*n).choose n ∣ ∑ k ∈ range (n + 1), T_term k * T_term (n - k) := sorry
    have h3 : ↑((2*n - 1) * (3*n).choose n) ∣ (↑(∑ k ∈ range (n + 1), T_term k * T_term (n - k)) : ℤ) := by exact_mod_cast h
    push_cast at h3
    have h4 : ((2*n - 1 : ℕ) : ℤ) = (2 * ↑n - 1) := by omega
    rw [h4] at h3
    exact h3
