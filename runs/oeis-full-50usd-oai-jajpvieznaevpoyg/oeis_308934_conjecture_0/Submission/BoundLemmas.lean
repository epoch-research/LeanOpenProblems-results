import FormalConjectures.Util.ProblemImports
open Nat Finset

#check Nat.log_eq_iff
#check Nat.log_eq_of_pow_le_of_lt_pow
#check Nat.le_log_of_pow_le
#check Nat.log_lt_iff_lt_pow
#check Nat.pow_le_pow_iff_right
#check Nat.pow_le_pow_left
#check pow_le_pow_left₀
#check Nat.le_sqrt
#check Nat.le_sqrt'
#check Nat.sqrt_le
#check Nat.sqrt_lt

lemma y_bound_of_two_mul_sq_le (n y : ℕ) (h : 2 * y^2 ≤ n) : y < Nat.sqrt (n / 2) + 1 := by
  have hy2 : y^2 ≤ n / 2 := by
    exact Nat.le_div_iff_mul_le (by decide : 0 < 2) |>.2 (by simpa [mul_comm] using h)
  have hy : y ≤ Nat.sqrt (n / 2) := Nat.le_sqrt'.2 hy2
  omega

lemma exp2_bound_of_sq_le (n a b : ℕ) (hn : 0 < n) (h : (2^a * 3^b)^2 ≤ n) :
    a < Nat.log 2 n / 2 + 1 := by
  have h2pos : 0 < 2 := by decide
  have hbase : 2^(2*a) ≤ n := by
    calc
      2^(2*a) = (2^a)^2 := by rw [← pow_mul]; ring_nf
      _ ≤ (2^a * 3^b)^2 := by
        exact pow_le_pow_left₀ (Nat.zero_le _) (Nat.le_mul_of_pos_right (2^a) (pow_pos (by decide : 0 < 3) b)) 2
      _ ≤ n := h
  have hlog : 2*a ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide : 1 < 2) hbase
  omega

lemma exp3_bound_of_sq_le (n a b : ℕ) (hn : 0 < n) (h : (2^a * 3^b)^2 ≤ n) :
    b < Nat.log 3 n / 2 + 1 := by
  have hbase : 3^(2*b) ≤ n := by
    calc
      3^(2*b) = (3^b)^2 := by rw [← pow_mul]; ring_nf
      _ ≤ (2^a * 3^b)^2 := by
        have hb : 3^b ≤ 2^a * 3^b := Nat.le_mul_of_pos_left (3^b) (pow_pos (by decide : 0 < 2) a)
        exact pow_le_pow_left₀ (Nat.zero_le _) hb 2
      _ ≤ n := h
  have hlog : 2*b ≤ Nat.log 3 n := Nat.le_log_of_pow_le (by decide : 1 < 3) hbase
  omega
