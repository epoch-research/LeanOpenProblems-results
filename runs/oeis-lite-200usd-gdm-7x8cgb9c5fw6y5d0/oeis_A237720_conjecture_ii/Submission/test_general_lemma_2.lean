import FormalConjectures.Util.ProblemImports

open Nat

lemma conditional_proof_general (n : ℕ) (hn : n ≥ 3) (Q : ℕ) (hQ_prime : Q.Prime) (p : ℕ) (hp_prime : p.Prime) (hp_lt : p < n) (h_ge : Q * Q ≤ n + p) (h_le : n + p ≤ Q * Q + 2 * Q) :
    ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime := by
  refine ⟨p, hp_prime, hp_lt, ?_⟩
  have h_eq : n + p = Q * Q + (n + p - Q * Q) := by omega
  have h_a_le : n + p - Q * Q ≤ Q + Q := by omega
  have h_sqrt : sqrt (Q * Q + (n + p - Q * Q)) = Q := sqrt_add_eq Q h_a_le
  rw [← h_eq] at h_sqrt
  rw [h_sqrt]
  exact hQ_prime
