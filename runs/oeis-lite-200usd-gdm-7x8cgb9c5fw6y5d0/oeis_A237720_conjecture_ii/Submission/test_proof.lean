import FormalConjectures.Util.ProblemImports

open Nat

lemma conditional_proof (n : ℕ) (hn : n ≥ 30003) (Q : ℕ) (hQ_prime : Q.Prime) (hQ1 : sqrt n < Q) (h_fit : Q * Q - 2 * Q ≤ n) (h_small : 2 * (Q * Q - n) < n) :
    ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime := by
  have h_Q2 : Q * Q > n := by
    rwa [sqrt_lt] at hQ1
  have h_diff_pos : Q * Q - n ≠ 0 := by
    omega
  obtain ⟨p, hp_prime, hp1, hp2⟩ := exists_prime_lt_and_le_two_mul (Q * Q - n) h_diff_pos
  refine ⟨p, hp_prime, ?_, ?_⟩
  · omega
  · generalize hC : Q * Q = C at *
    have h_le : n + p ≤ C + 2 * Q := by
      calc n + p ≤ n + 2 * (C - n) := by omega
      _ = 2 * C - n := by omega
      _ ≤ C + 2 * Q := by omega
    have h_ge : C ≤ n + p := by omega
    have h_eq : n + p = C + (n + p - C) := by omega
    have h_a_le : n + p - C ≤ Q + Q := by omega
    rw [← hC] at h_eq h_a_le
    have h_sqrt : sqrt (Q * Q + (n + p - Q * Q)) = Q := sqrt_add_eq Q h_a_le
    rw [← h_eq] at h_sqrt
    rw [h_sqrt]
    exact hQ_prime

lemma conditional_proof_small (n : ℕ) (hn : n ≥ 30003) (Q : ℕ) (hQ_prime : Q.Prime) (hQ1 : Q * Q ≤ n + 1) (hQ2 : n ≤ Q * Q + 2 * Q - 4) :
    ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime := by
  have h_two_pos : 2 ≠ 0 := by omega
  obtain ⟨p, hp_prime, hp1, hp2⟩ := exists_prime_lt_and_le_two_mul 2 h_two_pos
  refine ⟨p, hp_prime, ?_, ?_⟩
  · omega
  · have h_le : n + p ≤ Q * Q + 2 * Q := by omega
    have h_ge : Q * Q ≤ n + p := by omega
    have h_eq : n + p = Q * Q + (n + p - Q * Q) := by omega
    have h_a_le : n + p - Q * Q ≤ Q + Q := by omega
    have h_sqrt : sqrt (Q * Q + (n + p - Q * Q)) = Q := sqrt_add_eq Q h_a_le
    rw [← h_eq] at h_sqrt
    rw [h_sqrt]
    exact hQ_prime


#print axioms conditional_proof
#print axioms conditional_proof_small
