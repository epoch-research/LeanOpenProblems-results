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
