import Mathlib

open Nat Real

noncomputable def A318199 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let result_real : ℝ := (n : ℝ) ^ ((p_n : ℝ) / n)
    (Int.toNat (floor result_real))

lemma A318199_val (n p v : ℕ) (hn : n > 0) (hp : Nat.nth Nat.Prime (n - 1) = p)
    (h_lower : v^n ≤ n^p) (h_upper : n^p < (v+1)^n) : A318199 n = v := by
  sorry
