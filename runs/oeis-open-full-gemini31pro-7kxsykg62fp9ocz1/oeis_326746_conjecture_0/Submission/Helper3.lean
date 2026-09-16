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

lemma S_100 (q d : ℕ) (hd : d < 100) : S (100 * q + d) = S q + d / 10 + d % 10 := by
  have : 100 * q + d = 10 * (10 * q + d / 10) + d % 10 := by omega
  rw [this]
  rw [S_10 (10 * q + d / 10) (d % 10) (by omega)]
  rw [S_10 q (d / 10) (by omega)]

def f (k C : ℕ) : ℕ := (k + 1) ^ C

lemma W_bound_base (C : ℕ) : (List.range (10^0)).countP (fun n => S n ≤ C) ≤ f 0 C := by
  simp [f]
  split <;> omega
