import FormalConjectures.Util.ProblemImports

open BigOperators Real

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  -- Summing over k=1 to n is equivalent to summing over k'=0 to n-1, where term index is k'+1.
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      -- Since k ≥ 1, exponent_int is non-negative. We use Int.toNat for the exponent of Int^Nat power.
      (-1 : ℤ) ^ exponent_int.toNat

lemma neg_one_pow_parity (n : ℕ) : (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases h_cases with h | h
  · rw [if_pos h]
    have hn : n = 2 * (n / 2) := by
      omega
    rw [hn]
    rw [pow_mul]
    simp
  · rw [if_neg (by omega)]
    have hn : n = 2 * (n / 2) + 1 := by
      omega
    rw [hn]
    rw [pow_add]
    rw [pow_mul]
    simp

lemma floor_three_half_power (k : ℕ) : ⌊((3 : ℝ) / 2) ^ k⌋ = ((3 : ℤ)^k) / ((2 : ℤ)^k) := by
  rw [floor_eq_iff]
  have h2k : (0 : ℝ) < (((2 : ℤ)^k : ℤ) : ℝ) := by positivity
  have h2k_int : (0 : ℤ) < (2 : ℤ)^k := by positivity
  have h_pow : ((3 : ℝ) / 2) ^ k = (↑((3 : ℤ)^k) / ↑((2 : ℤ)^k) : ℝ) := by
    rw [div_pow]
    push_cast
    rfl
  rw [h_pow]
  constructor
  · rw [le_div_iff₀ h2k]
    have h_int : ((3 : ℤ)^k) / ((2 : ℤ)^k) * ((2 : ℤ)^k) ≤ (3 : ℤ)^k := by
      apply Int.ediv_mul_le
      exact ne_of_gt h2k_int
    have h_real : ((((3 : ℤ)^k) / ((2 : ℤ)^k) * ((2 : ℤ)^k) : ℤ) : ℝ) ≤ (((3 : ℤ)^k : ℤ) : ℝ) := by
      exact_mod_cast h_int
    push_cast at h_real ⊢
    exact h_real
  · rw [div_lt_iff₀ h2k]
    have h_int : (3 : ℤ)^k < (((3 : ℤ)^k) / ((2 : ℤ)^k) + 1) * ((2 : ℤ)^k) := by
      apply Int.lt_ediv_add_one_mul_self
      exact h2k_int
    have h_real : (((3 : ℤ)^k : ℤ) : ℝ) < (((((3 : ℤ)^k) / ((2 : ℤ)^k) + 1) * ((2 : ℤ)^k) : ℤ) : ℝ) := by
      exact_mod_cast h_int
    push_cast at h_real ⊢
    exact h_real
