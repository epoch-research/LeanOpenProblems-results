import FormalConjectures.Util.ProblemImports

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac



lemma pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Monoid M] (x : M) {t e : ℕ}
    (h : x ^ t = 1) : x ^ e = x ^ (e % t) := by
  conv_lhs => rw [← Nat.mod_add_div e t]
  rw [pow_add, pow_mul, h, one_pow, mul_one]

lemma mul_pow_period {M : Type*} [Monoid M] {c y : M} (h : c * y = c) (k : ℕ) :
    c * y ^ k = c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, h]

lemma exp_mod_period (t q n : ℕ) (h : (2 : ZMod t) ^ 2 * (((2 : ZMod t) ^ 10) ^ q) = (2 : ZMod t) ^ 2) :
    (2 ^ (10 * n + 2) : ℕ) % t = (2 ^ (10 * (n % q) + 2) : ℕ) % t := by
  apply (ZMod.natCast_eq_natCast_iff (2 ^ (10 * n + 2)) (2 ^ (10 * (n % q) + 2)) t).mp
  norm_num only [Nat.cast_pow]
  have h1 : (2 : ZMod t) ^ (10 * n + 2) = (2 : ZMod t) ^ 2 * ((2 : ZMod t) ^ 10) ^ n := by
    rw [← pow_mul, ← pow_add]
    ring
  have h2 : (2 : ZMod t) ^ (10 * (n % q) + 2) = (2 : ZMod t) ^ 2 * ((2 : ZMod t) ^ 10) ^ (n % q) := by
    rw [← pow_mul, ← pow_add]
    ring
  rw [h1, h2]
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [pow_add, pow_mul]
  calc
    (2 : ZMod t) ^ 2 * (((2 : ZMod t) ^ 10) ^ (n % q) * (((2 : ZMod t) ^ 10) ^ q) ^ (n / q))
        = ((2 : ZMod t) ^ 2 * ((((2 : ZMod t) ^ 10) ^ q) ^ (n / q))) * (((2 : ZMod t) ^ 10) ^ (n % q)) := by ring
    _ = (2 : ZMod t) ^ 2 * (((2 : ZMod t) ^ 10) ^ (n % q)) := by
      rw [mul_pow_period h]

lemma not_dvd_2 (n : ℕ) : ¬ 2 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 2) 2 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  have hbase : (2 : ZMod 2) = 0 := by decide
  rw [hbase]
  change ¬ (0 ^ (2 ^ (10 * n + 2) + 2) + 1 = 0)
  simp

lemma not_dvd_17 (n : ℕ) : ¬ 17 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 17) 17 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 17) (t := 8)]
  · cases n with
    | zero => decide
    | succ n =>
      have he : (2 ^ (10 * (n + 1) + 2) + 2) % 8 = 2 := by
        have hdvd : 8 ∣ 2 ^ (10 * (n + 1) + 2) := by
          rw [show (8:ℕ) = 2 ^ 3 by norm_num]
          exact pow_dvd_pow 2 (by omega : 3 ≤ 10 * (n + 1) + 2)
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd]
      rw [he]
      decide
  · decide

lemma not_dvd_3 (n : ℕ) : ¬ 3 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 3) 3 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (t := 2)]
  · have he0 := exp_mod_period 2 1 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 2 = (2 ^ (10 * (n % 1) + 2) + 2) % 2 := by omega
    rw [he]
    have hn : n % 1 < 1 := Nat.mod_lt _ (by decide)
    interval_cases n % 1 <;> decide
  · decide

lemma not_dvd_5 (n : ℕ) : ¬ 5 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 5) 5 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 5) (t := 4)]
  · have he0 := exp_mod_period 4 1 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 4 = (2 ^ (10 * (n % 1) + 2) + 2) % 4 := by omega
    rw [he]
    have hn : n % 1 < 1 := Nat.mod_lt _ (by decide)
    interval_cases n % 1 <;> decide
  · decide

lemma not_dvd_7 (n : ℕ) : ¬ 7 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 7) 7 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 7) (t := 3)]
  · have he0 := exp_mod_period 3 1 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 3 = (2 ^ (10 * (n % 1) + 2) + 2) % 3 := by omega
    rw [he]
    have hn : n % 1 < 1 := Nat.mod_lt _ (by decide)
    interval_cases n % 1 <;> decide
  · decide

lemma not_dvd_11 (n : ℕ) : ¬ 11 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 11) 11 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 11) (t := 10)]
  · have he0 := exp_mod_period 10 2 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 10 = (2 ^ (10 * (n % 2) + 2) + 2) % 10 := by omega
    rw [he]
    have hn : n % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases n % 2 <;> decide
  · decide

lemma not_dvd_13 (n : ℕ) : ¬ 13 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 13) 13 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 13) (t := 12)]
  · have he0 := exp_mod_period 12 1 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 12 = (2 ^ (10 * (n % 1) + 2) + 2) % 12 := by omega
    rw [he]
    have hn : n % 1 < 1 := Nat.mod_lt _ (by decide)
    interval_cases n % 1 <;> decide
  · decide

lemma not_dvd_19 (n : ℕ) : ¬ 19 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 19) 19 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 19) (t := 18)]
  · have he0 := exp_mod_period 18 3 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 18 = (2 ^ (10 * (n % 3) + 2) + 2) % 18 := by omega
    rw [he]
    have hn : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases n % 3 <;> decide
  · decide

lemma not_dvd_23 (n : ℕ) : ¬ 23 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 23) 23 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 23) (t := 11)]
  · have he0 := exp_mod_period 11 1 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 11 = (2 ^ (10 * (n % 1) + 2) + 2) % 11 := by omega
    rw [he]
    have hn : n % 1 < 1 := Nat.mod_lt _ (by decide)
    interval_cases n % 1 <;> decide
  · decide

lemma not_dvd_29 (n : ℕ) : ¬ 29 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 29) 29 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 29) (t := 28)]
  · have he0 := exp_mod_period 28 3 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 28 = (2 ^ (10 * (n % 3) + 2) + 2) % 28 := by omega
    rw [he]
    have hn : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases n % 3 <;> decide
  · decide

lemma not_dvd_31 (n : ℕ) : ¬ 31 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 31) 31 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 31) (t := 5)]
  · have he0 := exp_mod_period 5 2 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 5 = (2 ^ (10 * (n % 2) + 2) + 2) % 5 := by omega
    rw [he]
    have hn : n % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases n % 2 <;> decide
  · decide

lemma not_dvd_37 (n : ℕ) : ¬ 37 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 37) 37 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 37) (t := 36)]
  · have he0 := exp_mod_period 36 3 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 36 = (2 ^ (10 * (n % 3) + 2) + 2) % 36 := by omega
    rw [he]
    have hn : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases n % 3 <;> decide
  · decide

lemma not_dvd_41 (n : ℕ) : ¬ 41 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 41) 41 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 41) (t := 20)]
  · have he0 := exp_mod_period 20 2 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 20 = (2 ^ (10 * (n % 2) + 2) + 2) % 20 := by omega
    rw [he]
    have hn : n % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases n % 2 <;> decide
  · decide

lemma not_dvd_43 (n : ℕ) : ¬ 43 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 43) 43 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 43) (t := 14)]
  · have he0 := exp_mod_period 14 3 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 14 = (2 ^ (10 * (n % 3) + 2) + 2) % 14 := by omega
    rw [he]
    have hn : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases n % 3 <;> decide
  · decide

lemma not_dvd_47 (n : ℕ) : ¬ 47 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 47) 47 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 47) (t := 23)]
  · have he0 := exp_mod_period 23 11 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 23 = (2 ^ (10 * (n % 11) + 2) + 2) % 23 := by omega
    rw [he]
    have hn : n % 11 < 11 := Nat.mod_lt _ (by decide)
    interval_cases n % 11 <;> decide
  · decide

lemma not_dvd_53 (n : ℕ) : ¬ 53 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 53) 53 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 53) (t := 52)]
  · have he0 := exp_mod_period 52 6 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 52 = (2 ^ (10 * (n % 6) + 2) + 2) % 52 := by omega
    rw [he]
    have hn : n % 6 < 6 := Nat.mod_lt _ (by decide)
    interval_cases n % 6 <;> decide
  · decide

lemma not_dvd_59 (n : ℕ) : ¬ 59 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 59) 59 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 59) (t := 58)]
  · have he0 := exp_mod_period 58 14 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 58 = (2 ^ (10 * (n % 14) + 2) + 2) % 58 := by omega
    rw [he]
    have hn : n % 14 < 14 := Nat.mod_lt _ (by decide)
    interval_cases n % 14 <;> decide
  · decide

lemma not_dvd_61 (n : ℕ) : ¬ 61 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 61) 61 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 61) (t := 60)]
  · have he0 := exp_mod_period 60 2 n (by decide)
    have he : (2 ^ (10 * n + 2) + 2) % 60 = (2 ^ (10 * (n % 2) + 2) + 2) % 60 := by omega
    rw [he]
    have hn : n % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases n % 2 <;> decide
  · decide


lemma exp_mod_66 (n : ℕ) : (2 ^ (10 * n + 2) : ℕ) % 66 = 4 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hpow : 2 ^ (10 * (n + 1) + 2) = 2 ^ (10 * n + 2) * 2 ^ 10 := by
      rw [← pow_add]
      congr 1
    rw [hpow, Nat.mul_mod, ih]
    norm_num

lemma dvd_67 (n : ℕ) : 67 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 67) 67 (2 ^ (2 ^ (10 * n + 2) + 2) + 3)]
  norm_num only [Nat.cast_add, Nat.cast_pow]
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 67) (t := 66)]
  · have he0 := exp_mod_66 n
    rw [show (2 ^ (10 * n + 2) + 2) % 66 = 6 by omega]
    decide
  · decide

/-- OEIS A248802 Conjecture 1: a(10n+2) = 67 for n >= 0. -/
theorem oeis_248802_conjecture_0 (n : ℕ) : a (10 * n + 2) = 67 := by
  unfold a
  let N := 2 ^ (2 ^ (10 * n + 2) + 2) + 3
  change Nat.minFac N = 67
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd (by norm_num) (dvd_67 n)
  · by_contra hnot
    have hlt : Nat.minFac N < 67 := by omega
    have hNne1 : N ≠ 1 := by
      have hp : 0 < 2 ^ (2 ^ (10 * n + 2) + 2) := pow_pos (by norm_num) _
      omega
    have hpmin : Nat.Prime (Nat.minFac N) := Nat.minFac_prime hNne1
    have hdvd : Nat.minFac N ∣ N := Nat.minFac_dvd N
    have hmge : 2 ≤ Nat.minFac N := hpmin.two_le
    interval_cases Nat.minFac N <;> first | exact not_dvd_2 n hdvd | exact not_dvd_3 n hdvd | exact not_dvd_5 n hdvd | exact not_dvd_7 n hdvd | exact not_dvd_11 n hdvd | exact not_dvd_13 n hdvd | exact not_dvd_17 n hdvd | exact not_dvd_19 n hdvd | exact not_dvd_23 n hdvd | exact not_dvd_29 n hdvd | exact not_dvd_31 n hdvd | exact not_dvd_37 n hdvd | exact not_dvd_41 n hdvd | exact not_dvd_43 n hdvd | exact not_dvd_47 n hdvd | exact not_dvd_53 n hdvd | exact not_dvd_59 n hdvd | exact not_dvd_61 n hdvd | contradiction
