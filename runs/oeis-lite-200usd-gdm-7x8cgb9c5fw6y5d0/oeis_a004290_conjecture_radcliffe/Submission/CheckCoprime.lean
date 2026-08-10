import Mathlib

open Nat

theorem test (k : ℕ) (hk2 : k ≥ 2) (c d : ℕ) 
  (hd_pos : d > 0) (hd_cop : Nat.Coprime d 10) 
  (hd2c_le : d * 2 ^ c < 10 ^ k - 1) (h_cd_gt : c + d ≥ 9 * k) 
  (L : ℕ) (hL_ge : L ≥ 15) (h_mono : 10 ^ 15 ≤ 10 ^ L) (hd9999 : d ≤ 3) : False := by
  interval_cases d <;> (try { revert hd_cop; intro h_cop; contradiction })
  sorry
