import Submission.Spec
open Nat Finset

lemma type_of_lemma_disproof : (type_of% @oeis_a189286_conjecture_0) = ∀ (n : ℕ),
  if n = 0 then True else
    have numerator_int : ℤ := ∑ k ∈ Finset.range (n + 1), ↑(T_term k) * ↑(T_term (n - k));
    have denominator : ℤ := (2 * ↑n - 1) * ↑((3 * n).choose n);
    denominator ∣ numerator_int := rfl

lemma t_div_d (k m : ℕ) : (2*(k+m) - 1) * (3*(k+m)).choose (k+m) ∣ T_term k * T_term m := by
  sorry

lemma sum_div (n : ℕ) : (2*n - 1) * (3*n).choose n ∣ ∑ k ∈ range (n + 1), T_term k * T_term (n - k) := by
  apply dvd_sum
  intro k hk
  rw [mem_range] at hk
  have h := t_div_d k (n - k)
  have h2 : k + (n - k) = n := by omega
  rw [h2] at h
  exact h

theorem proof_test : type_of% @oeis_a189286_conjecture_0 := by
  rw [type_of_lemma_disproof]
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    have h := sum_div n
    have h3 : ↑((2*n - 1) * (3*n).choose n) ∣ (↑(∑ k ∈ range (n + 1), T_term k * T_term (n - k)) : ℤ) := by
      apply Int.natCast_dvd_natCast.mpr h
    have h4 : ((2*n - 1 : ℕ) : ℤ) = (2 * ↑n - 1) := by 
      have h_pos : 1 ≤ 2*n := by omega
      omega
    have h5 : ↑((2*n - 1) * (3*n).choose n) = ((2*n - 1 : ℕ) : ℤ) * ((3*n).choose n : ℤ) := by exact Nat.cast_mul _ _
    rw [h5, h4] at h3
    have h6 : (↑(∑ k ∈ range (n + 1), T_term k * T_term (n - k)) : ℤ) = ∑ k ∈ range (n + 1), (↑(T_term k * T_term (n - k)) : ℤ) := by exact Nat.cast_sum _ _
    rw [h6] at h3
    have h7 : (∑ k ∈ range (n + 1), (↑(T_term k * T_term (n - k)) : ℤ)) = ∑ k ∈ range (n + 1), (↑(T_term k) : ℤ) * ↑(T_term (n - k)) := by
      apply sum_congr rfl
      intro x hx
      exact Nat.cast_mul _ _
    rw [h7] at h3
    exact h3
