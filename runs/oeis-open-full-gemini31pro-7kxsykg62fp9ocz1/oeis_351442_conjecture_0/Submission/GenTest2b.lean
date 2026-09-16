import Submission.GenTest2a
open Nat Finset
lemma A003958_sigma_n1 : A003958 (ArithmeticFunction.sigma 1 n1) = n1 := by
  rw [sigma_n1]
  dsimp [P_2, P_3, P_5, P_7, P_13, P_17]
  rw [sigma_2_13]
  rw [sigma_3_6]
  rw [sigma_5_1]
  rw [sigma_7_6]
  rw [sigma_13_4]
  rw [sigma_17_2]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_mul (by norm_num) (by norm_num)]
  rw [A003958_sig_2_13]
  rw [A003958_sig_3_6]
  rw [A003958_sig_5_1]
  rw [A003958_sig_7_6]
  rw [A003958_sig_13_4]
  rw [A003958_sig_17_2]
  dsimp [n1]
  dsimp [P_2, P_3, P_5, P_7, P_13, P_17]
  norm_num

theorem oeis_351442_conjecture_0.disproof : ¬ (∀ n : ℕ, n > 0 → (a_test n = n ↔ n ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ))) := by
  intro h
  have h_pos : 0 < n1 := by norm_num [n1, P_2, P_3, P_5, P_7, P_13, P_17]
  have h1 := h n1 h_pos
  have h2 : a_test n1 = n1 := A003958_sigma_n1
  have h3 : n1 ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ) := h1.mp h2
  revert h3
  decide

