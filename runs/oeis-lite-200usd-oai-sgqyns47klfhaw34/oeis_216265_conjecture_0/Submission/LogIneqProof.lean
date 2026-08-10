import FormalConjectures.Util.ProblemImports

open Nat

lemma cube_succ_le_two_mul_cube_of_ten_le {n : ℕ} (hn : 10 ≤ n) :
    (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
  nlinarith [sq_nonneg (n : ℤ), hn]

lemma cube_lt_two_pow_succ_of_ten_le {n : ℕ} (hn : 10 ≤ n) : n ^ 3 < 2 ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1) ^ 3 ≤ 2 * n ^ 3 := cube_succ_le_two_mul_cube_of_ten_le hn
        _ < 2 * 2 ^ (n + 1) := (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 ih
        _ = 2 ^ (n + 1 + 1) := by
          conv_rhs => rw [show n + 1 + 1 = (n + 1).succ by omega, Nat.pow_succ']

lemma log_cube_le_self_of_two_le {n p : ℕ} (hn : 10 ≤ n) (hp2 : 2 ≤ p) :
    Nat.log p (n ^ 3) ≤ n := by
  have hlt2 : n ^ 3 < 2 ^ (n + 1) := cube_lt_two_pow_succ_of_ten_le hn
  have hpow : 2 ^ (n + 1) ≤ p ^ (n + 1) := Nat.pow_le_pow_left hp2 (n + 1)
  have hlt : n ^ 3 < p ^ (n + 1) := lt_of_lt_of_le hlt2 hpow
  have hn3ne : n ^ 3 ≠ 0 := by positivity
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hn3ne hlt)

lemma log_cube_le_div_cube_sub_self {n p : ℕ} (hn : 14 ≤ n) (hp2 : 2 ≤ p)
    (hle : p ≤ n ^ 3 - n) :
    Nat.log p (n ^ 3) ≤ (n ^ 3 - n) / p := by
  have hn10 : 10 ≤ n := by omega
  have hlogn : Nat.log p (n ^ 3) ≤ n := log_cube_le_self_of_two_le hn10 hp2
  by_cases hsmall : p ≤ n ^ 2 - 1
  · have hnp : n ≤ (n ^ 3 - n) / p := by
      -- n * p ≤ n^3 - n follows from p ≤ n^2 - 1.
      have hnpos : 0 < n := by omega
      have hmulle : n * p ≤ n ^ 3 - n := by
        calc
          n * p ≤ n * (n ^ 2 - 1) := Nat.mul_le_mul_left n hsmall
          _ = n ^ 3 - n := by
            rw [Nat.mul_sub_left_distrib, mul_one]
            ring_nf
      exact (Nat.le_div_iff_mul_le (by omega : 0 < p)).2 (by simpa [mul_comm] using hmulle)
    exact hlogn.trans hnp
  · have hgt : n ^ 2 - 1 < p := Nat.lt_of_not_ge hsmall
    have hp2gt : n ^ 3 < p ^ 2 := by
      -- since p > n^2 -1 and n≥14, p^2 > n^3
      have hpge : n ^ 2 ≤ p := by omega
      calc
        n ^ 3 < (n ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (n : ℤ), hn]
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hpge 2
    have hloglt : Nat.log p (n ^ 3) < 2 := by
      exact Nat.log_lt_of_lt_pow (by positivity : n ^ 3 ≠ 0) hp2gt
    have hlogle1 : Nat.log p (n ^ 3) ≤ 1 := by omega
    have hdivpos : 1 ≤ (n ^ 3 - n) / p := by
      exact Nat.succ_le_iff.mpr (Nat.div_pos hle (by omega : 0 < p))
    exact hlogle1.trans hdivpos
