import Mathlib

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

lemma S_10 (q d : ℕ) (hd : d < 10) : S (10 * q + d) = S q + d := by
  by_cases hq : q = 0
  · simp [hq, S]
    cases d with
    | zero => simp
    | succ d =>
      have : d + 1 < 10 := hd
      rw [Nat.digits_of_lt _ _ (by omega) (by omega)]
      simp
  · have h1 : 10 * q + d > 0 := by omega
    have h2 : 1 < 10 := by decide
    unfold S
    rw [Nat.digits_def' h2 h1]
    have h3 : (10 * q + d) % 10 = d := by omega
    have h4 : (10 * q + d) / 10 = q := by omega
    rw [h3, h4]
    simp [add_comm]

lemma S_add_pow (k j i : ℕ) (hj : j < 10) (hi : i < 10^k) :
  S (10^k * j + i) = j + S i := by
  induction k generalizing i with
  | zero =>
    have : i = 0 := by omega
    rw [this]
    simp
    have eqj : S j = S (10 * 0 + j) := by congr 1; omega
    rw [eqj, S_10 0 j hj]
    simp [S]
  | succ k ih =>
    have h_div : i / 10 < 10^k := by
      have h1 : 10^(k+1) = 10 * 10^k := by ring
      have h2 : i < 10^k * 10 := by linarith
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h2
    have eq : 10^(k+1) * j + i = 10 * (10^k * j + i / 10) + i % 10 := by
      have h1 : 10^(k+1) = 10 * 10^k := by ring
      rw [h1]
      have h2 : i = 10 * (i / 10) + i % 10 := Nat.div_add_mod i 10 |>.symm
      have : 10 * 10^k * j + i = 10 * (10^k * j) + i := by ring
      rw [this]
      nth_rw 1 [h2]
      ring
    rw [eq]
    rw [S_10 _ (i % 10) (by omega)]
    have h_Si : S i = S (10 * (i / 10) + i % 10) := by
      have h2 : i = 10 * (i / 10) + i % 10 := Nat.div_add_mod i 10 |>.symm
      nth_rw 1 [h2]
    rw [h_Si]
    rw [S_10 (i / 10) (i % 10) (by omega)]
    rw [ih (i / 10) h_div]
    omega
