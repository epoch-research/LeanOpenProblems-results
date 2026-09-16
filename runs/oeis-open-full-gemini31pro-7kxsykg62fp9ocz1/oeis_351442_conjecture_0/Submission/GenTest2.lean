import Submission.GenTest1
open Nat Finset
def P_2 : ℕ := 2^13
def P_3 : ℕ := 3^6
def P_5 : ℕ := 5^1
def P_7 : ℕ := 7^6
def P_13 : ℕ := 13^4
def P_17 : ℕ := 17^2
def n1 : ℕ := P_2 * P_3 * P_5 * P_7 * P_13 * P_17
lemma sigma_n1 : ArithmeticFunction.sigma 1 n1 = ArithmeticFunction.sigma 1 P_2 * ArithmeticFunction.sigma 1 P_3 * ArithmeticFunction.sigma 1 P_5 * ArithmeticFunction.sigma 1 P_7 * ArithmeticFunction.sigma 1 P_13 * ArithmeticFunction.sigma 1 P_17 := by
  dsimp [n1]
  have h_gcd_5 : (P_2 * P_3 * P_5 * P_7 * P_13).gcd P_17 = 1 := by norm_num [P_2, P_3, P_5, P_7, P_13, P_17]
  rw [sigma_mul_coprime h_gcd_5]
  have h_gcd_4 : (P_2 * P_3 * P_5 * P_7).gcd P_13 = 1 := by norm_num [P_2, P_3, P_5, P_7, P_13, P_17]
  rw [sigma_mul_coprime h_gcd_4]
  have h_gcd_3 : (P_2 * P_3 * P_5).gcd P_7 = 1 := by norm_num [P_2, P_3, P_5, P_7, P_13, P_17]
  rw [sigma_mul_coprime h_gcd_3]
  have h_gcd_2 : (P_2 * P_3).gcd P_5 = 1 := by norm_num [P_2, P_3, P_5, P_7, P_13, P_17]
  rw [sigma_mul_coprime h_gcd_2]
  have h_gcd_1 : (P_2).gcd P_3 = 1 := by norm_num [P_2, P_3, P_5, P_7, P_13, P_17]
  rw [sigma_mul_coprime h_gcd_1]
  norm_num

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

