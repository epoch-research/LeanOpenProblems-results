import FormalConjectures.Util.ProblemImports

open Nat

lemma cover_lemma (n : ℕ) (Q p L : ℕ) (hQ : Q.Prime) (hp : p.Prime) (h1 : Q * Q - p ≤ n) (h2 : n ≤ Q * Q + 2 * Q - p) (hL : L ≤ n) (hp_lt : p < L) :
    ∃ p', p'.Prime ∧ p' < n ∧ (sqrt (n + p')).Prime := by
  refine ⟨p, hp, ?_, ?_⟩
  · omega
  · have h_ge : Q * Q ≤ n + p := by omega
    have h_le : n + p ≤ Q * Q + 2 * Q := by omega
    have h_eq : n + p = Q * Q + (n + p - Q * Q) := by omega
    have h_a_le : n + p - Q * Q ≤ Q + Q := by omega
    have h_sqrt : sqrt (Q * Q + (n + p - Q * Q)) = Q := sqrt_add_eq Q h_a_le
    rw [← h_eq] at h_sqrt
    rw [h_sqrt]
    exact hQ

theorem test_case_3_6 (n : ℕ) (hn : n ≥ 3) (hn2 : n ≤ 6) : ∃ p, p.Prime ∧ p < n ∧ (sqrt (n + p)).Prime := by
  exact cover_lemma n 2 2 3 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by decide)
