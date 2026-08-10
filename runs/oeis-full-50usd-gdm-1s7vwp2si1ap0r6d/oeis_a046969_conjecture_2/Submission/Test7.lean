import FormalConjectures.Util.ProblemImports

open Rat Nat

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

lemma a_num_den_relation (n : ℕ) (hn : 2 ≤ n) : (bernoulli (2 * n)).num * (a n : ℤ) = (bernoulli (2 * n) / ((2 * n * (2 * n - 1) : ℕ) : ℚ)).num * (bernoulli (2 * n)).den * ((2 * n * (2 * n - 1) : ℕ) : ℤ) := by
  unfold a
  have h_ne : n ≠ 0 := by omega
  simp only [h_ne, ↓reduceIte]
  let m := 2 * n
  let k := m * (m - 1)
  have hk_pos : 0 < k := by
    change 0 < (2 * n) * (2 * n - 1)
    apply Nat.mul_pos
    · omega
    · omega
  have hk_ne : (k : ℚ) ≠ 0 := by
    exact_mod_cast hk_pos.ne'
  let q := bernoulli m
  let r := (k : ℚ)⁻¹
  have hr_num : r.num = 1 := by
    exact inv_natCast_num_of_pos hk_pos
  have hr_den : r.den = k := by
    exact inv_natCast_den_of_pos hk_pos
  have h_mul := Rat.mul_num_den' q r
  rw [hr_num, hr_den] at h_mul
  simp only [mul_one] at h_mul
  have h_div : q * r = q / (k : ℚ) := by
    exact div_eq_mul_inv q (k : ℚ)
  rw [h_div] at h_mul
  have h_mul_int : q.num * ((q / (k : ℚ)).den : ℤ) = ((q / (k : ℚ)).num * (q.den : ℤ) * (k : ℤ) : ℤ) := by
    rw [h_mul]
  exact h_mul_int

lemma dvd_a_mul (n : ℕ) (hn : 2 ≤ n) : ((2 * n * (2 * n - 1) : ℕ) : ℤ) ∣ (bernoulli (2 * n)).num * (a n : ℤ) := by
  rw [a_num_den_relation n hn]
  use (bernoulli (2 * n) / ((2 * n * (2 * n - 1) : ℕ) : ℚ)).num * (bernoulli (2 * n)).den
  ring


