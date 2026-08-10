import Submission.Spec

noncomputable def expected_p_th_prime (p : ℕ) : ℕ := _root_.Nat.nth Nat.Prime (p - 1)

#check (oeis_234694_conjecture_1 : ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧ (Nat.Prime (expected_p_th_prime p - p + 1) ∨ Nat.Prime (expected_p_th_prime p + p + 1)))
