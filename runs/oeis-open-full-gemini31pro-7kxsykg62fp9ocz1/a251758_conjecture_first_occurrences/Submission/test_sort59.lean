import Mathlib

lemma a_le_p_minus_1 (n p s k : ℕ) (hp : p > 0) (hn : n = p * k) (hk : k ≥ p)
  (hs : s ≥ k * n + p) :
  n^2 / s ≤ p - 1 := by
  have hs0 : s > 0 := by omega
  have hn2 : n^2 = p * (k * n) := by
    calc
      n^2 = n * n := by ring
      _ = (p * k) * n := by rw [hn]
      _ = p * (k * n) := by ring
  have h_ps : p * s ≥ p * (k * n + p) := Nat.mul_le_mul_left p hs
  have h_ps2 : p * s ≥ n^2 + p^2 := by
    calc
      p * s ≥ p * (k * n) + p * p := by
        have : p * (k * n + p) = p * (k * n) + p * p := Nat.mul_add p (k * n) p
        omega
      _ = n^2 + p^2 := by
        have : p * p = p^2 := by ring
        omega
  have h_lt : n^2 < p * s := by
    have : p^2 > 0 := by nlinarith
    omega
  have h_div : n^2 / s < p := (Nat.div_lt_iff_lt_mul hs0).mpr h_lt
  omega
