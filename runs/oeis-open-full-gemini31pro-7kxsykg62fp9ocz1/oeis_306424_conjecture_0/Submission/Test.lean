import Mathlib

lemma k_ge_289 (k : ℕ) (hk : k ≥ 289) : 
  let b := Nat.sqrt k
  let x := k - b * b
  b ≥ 17 ∧ x ≤ 2 * b := by
  intro b x
  have h1 : b * b ≤ k := Nat.sqrt_le k
  have h2 : k < (b + 1) * (b + 1) := Nat.lt_succ_sqrt k
  have h_exp : (b + 1) * (b + 1) = b * b + 2 * b + 1 := by ring
  have h_b : b ≥ 17 := by nlinarith
  have h_x_bound : x ≤ 2 * b := by omega
  exact ⟨h_b, h_x_bound⟩
