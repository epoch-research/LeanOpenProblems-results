import FormalConjectures.Util.ProblemImports
open Finset

lemma ceil_linear_sum_bound (n : ℕ) :
    3 * (∑ i ∈ Finset.range (n - 2), (2 * (i + 1) + n + 2) / 3)
      ≤ (n - 2) * (2 * n + 1) := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ t =>
        -- n is t+2
        simp
        calc
          3 * (∑ i ∈ Finset.range t, (2 * (i + 1) + (t + 1 + 1) + 2) / 3)
              = ∑ i ∈ Finset.range t, 3 * ((2 * (i + 1) + (t + 1 + 1) + 2) / 3) := by
                rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ Finset.range t, (2 * (i + 1) + (t + 1 + 1) + 2) := by
                apply Finset.sum_le_sum
                intro i hi
                exact Nat.mul_div_le (2 * (i + 1) + (t + 1 + 1) + 2) 3
          _ ≤ t * (2 * (t + 1 + 1) + 1) := by
                simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
                rw [← Finset.mul_sum]
                rw [Finset.sum_range_id]
                cases t with
                | zero => norm_num
                | succ u =>
                    simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
                    have hdiv : ((u + 1) * u / 2) * 2 ≤ (u + 1) * u := by
                      exact Nat.div_mul_le_self _ _
                    nlinarith [hdiv]


lemma q_le_div_of_threshold {n i k : ℕ} (hi : i ∈ Finset.range (n - 2))
    (hk : (2 * (i + 1) + n + 2) / 3 ≤ k) :
    i + 1 ≤ k ^ 2 / n := by
  have hnpos : 0 < n := by
    have : i < n - 2 := by simpa using hi
    omega
  rw [Nat.le_div_iff_mul_le hnpos]
  let q := i + 1
  let c := (2 * q + n + 2) / 3
  have hceil : 2 * q + n ≤ 3 * c := by
    dsimp [c]
    omega
  have hkc : c ≤ k := by simpa [q, c] using hk
  have h3 : 3 * c ≤ 3 * k := Nat.mul_le_mul_left 3 hkc
  have hagm : 9 * q * n ≤ (2 * q + n) ^ 2 := by
    have hz : (0 : ℤ) ≤ ((n : ℤ) - 2 * (q : ℤ)) ^ 2 := sq_nonneg _
    have hz' : (9 * q * n : ℤ) ≤ ((2 * q + n : ℕ) : ℤ) ^ 2 := by
      push_cast
      ring_nf at hz ⊢
      nlinarith
    exact_mod_cast hz'   
  have hmain : 9 * q * n ≤ (3 * k) ^ 2 := by
    nlinarith
  have hfinal : q * n ≤ k ^ 2 := by
    nlinarith
  simpa [q, pow_two, mul_assoc, mul_comm, mul_left_comm] using hfinal
