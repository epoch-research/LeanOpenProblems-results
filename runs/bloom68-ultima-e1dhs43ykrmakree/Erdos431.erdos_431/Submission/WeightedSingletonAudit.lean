import FormalConjecturesUtil

/-!
# Algebraic audit of weighted singleton corrections

These lemmas do not resolve the Ostmann problem. They isolate the diagonal
self-energy in a proposed weighted larger-sieve argument. In the application,
`p` is a prime, `r` is its representation count, `F` is the total weight on
frozen endpoints, and `H` is their sum of squared weights. Each factor has
normalized mass one.
-/

open scoped BigOperators

namespace WeightedSingletonAudit

/-- Gain over the pooled support-size baseline, before paying the diagonal. -/
noncomputable def pooledGain (p r F H : ℝ) : ℝ :=
  H + (2 - F) ^ 2 / (p - r) - 4 / (p + r)


/-- Cauchy--Schwarz with an upper bound for the number of occupied cells. -/
theorem mass_sq_div_bound_le {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (k : ℝ) (hk : 0 < k) (hcard : (s.card : ℝ) ≤ k) :
    (∑ i ∈ s, w i) ^ 2 / k ≤ ∑ i ∈ s, (w i) ^ 2 := by
  apply (div_le_iff₀ hk).2
  calc
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (w i) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ k * ∑ i ∈ s, (w i) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := mul_comm _ _

/-- The local lower bound after separating globally singleton cells. -/
theorem pooled_collision_lower {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (p r F H : ℝ) (hpr : r < p)
    (hcard : (s.card : ℝ) ≤ p - r) (hmass : (∑ i ∈ s, w i) = 2 - F) :
    H + (2 - F) ^ 2 / (p - r) ≤ H + ∑ i ∈ s, (w i) ^ 2 := by
  have h := mass_sq_div_bound_le s w (p - r) (sub_pos.mpr hpr) hcard
  rw [hmass] at h
  exact add_le_add_right h H

/-- Exact correction after subtracting the frozen endpoints' self-energy. -/
theorem after_diagonal_identity (p r F H : ℝ)
    (hm : p - r ≠ 0) (hp : p + r ≠ 0) :
    pooledGain p r F H - H =
      8 * r / (p ^ 2 - r ^ 2) - F * (4 - F) / (p - r) := by
  have hfactor : p ^ 2 - r ^ 2 = (p - r) * (p + r) := by ring
  unfold pooledGain
  rw [hfactor]
  field_simp
  ring

/-- Nonnegative endpoint weights cannot improve the post-diagonal bound. -/
theorem after_diagonal_le (p r F H : ℝ)
    (hr : 0 ≤ r) (hpr : r < p) (hF : 0 ≤ F) (hF' : F ≤ 2) :
    pooledGain p r F H - H ≤ 8 * r / (p ^ 2 - r ^ 2) := by
  have hm : 0 < p - r := sub_pos.mpr hpr
  have hp : 0 < p + r := by linarith
  rw [after_diagonal_identity p r F H (ne_of_gt hm) (ne_of_gt hp)]
  have hnonneg : 0 ≤ F * (4 - F) / (p - r) :=
    div_nonneg (mul_nonneg hF (by linarith)) hm.le
  linarith

/-- Sum-of-squares expression for the full, unsubtracted local gain. -/
theorem pooledGain_eq_squares {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (p r : ℝ) (hcard : (s.card : ℝ) = 2 * r)
    (hm : p - r ≠ 0) (hp : p + r ≠ 0) :
    pooledGain p r (∑ i ∈ s, z i) (∑ i ∈ s, (z i) ^ 2) =
      (∑ i ∈ s, (z i - 2 / (p + r)) ^ 2) +
        ((∑ i ∈ s, z i) - 4 * r / (p + r)) ^ 2 / (p - r) := by
  have hexpand :
      (∑ i ∈ s, (z i - 2 / (p + r)) ^ 2) =
        (∑ i ∈ s, (z i) ^ 2) - 4 / (p + r) * (∑ i ∈ s, z i) +
          (s.card : ℝ) * (2 / (p + r)) ^ 2 := by
    calc
      _ = ∑ i ∈ s, ((z i) ^ 2 - (4 / (p + r)) * z i +
          (2 / (p + r)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
  rw [hexpand, hcard]
  unfold pooledGain
  field_simp
  ring

/-- The sum-of-squares gain is nonnegative; its diagonal-free part need not be. -/
theorem pooledGain_nonneg {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (p r : ℝ) (hcard : (s.card : ℝ) = 2 * r)
    (hpr : r < p) :
    0 ≤ pooledGain p r (∑ i ∈ s, z i) (∑ i ∈ s, (z i) ^ 2) := by
  have hm : 0 < p - r := sub_pos.mpr hpr
  have hp : 0 < p + r := by linarith
  rw [pooledGain_eq_squares s z p r hcard (ne_of_gt hm) (ne_of_gt hp)]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (div_nonneg (sq_nonneg _) hm.le)

/-- A balanced local example refutes nonnegativity after diagonal subtraction. -/
theorem balanced_gain_zero : pooledGain 7 1 (1 / 2) (1 / 8) = 0 := by
  norm_num [pooledGain]

theorem balanced_after_diagonal_negative :
    pooledGain 7 1 (1 / 2) (1 / 8) - (1 / 8 : ℝ) < 0 := by
  rw [balanced_gain_zero]
  norm_num

end WeightedSingletonAudit
