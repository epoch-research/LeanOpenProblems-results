import FormalConjecturesUtil

/-! Future-baseline finite-measure inequalities. These are auxiliary results,
not an arithmetic covering obstruction or a complete transport comparison. -/
namespace Erdos7BaselineRetention
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Keeping the actual old-coordinate baseline avoids requiring it to be at
most one. Nonnegativity of the removed mass is essential above that threshold. -/
lemma defect_baseline_bound (mu D B L : ℚ) (hD0 : 0 ≤ D) (hD : D ≤ mu * L) :
    D * (1 - B) ≤ mu * L * max (1 - B) 0 := by
  by_cases h : B ≤ 1
  · rw [max_eq_left (by linarith)]
    exact mul_le_mul_of_nonneg_right hD (by linarith)
  · rw [max_eq_right (by linarith), mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hD0 (by linarith)

/-- The comparison concerns increments above an actual old-coordinate
baseline, not a hypothetical common random variable for different families. -/
theorem fiber_baseline_step {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : Ω → ℚ) (ν : Ω → A → ℚ) (F : Ω → A → ℚ)
    (D B L T : Ω → ℚ) (hD0 : ∀ x, 0 ≤ D x)
    (hmass : ∀ x, (∑ y, ν x y) = μ x - D x)
    (hfuture : (∑ x, ∑ y, ν x y) ≤ ∑ x, ∑ y, ν x y * F x y)
    (hloss : ∀ x, D x ≤ μ x * L x)
    (hcomparison : (∑ x, ∑ y, ν x y * (F x y - B x)) ≤ ∑ x, μ x * T x) :
    (∑ x, μ x) ≤ ∑ x, μ x * (B x + L x * max (1 - B x) 0 + T x) := by
  have hsplit : (∑ x, ∑ y, ν x y * F x y) =
      (∑ x, (μ x - D x) * B x) + ∑ x, ∑ y, ν x y * (F x y - B x) := by
    calc
      _ = ∑ x, ∑ y, (ν x y * B x + ν x y * (F x y - B x)) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul, hmass]
  have hmain := hfuture.trans (hsplit.le.trans (add_le_add le_rfl hcomparison))
  simp_rw [hmass] at hmain
  rw [Finset.sum_sub_distrib] at hmain
  have hbound : (∑ x, (μ x - D x) * B x) + (∑ x, μ x * T x) + (∑ x, D x) ≤
      ∑ x, μ x * (B x + L x * max (1 - B x) 0 + T x) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have hh := defect_baseline_bound (μ x) (D x) (B x) (L x) (hD0 x) (hloss x)
    nlinarith
  linarith

/-- The live cost is the maximum of two affine combinations. In applications,
`a - L ≥ 0` makes both combinations positive mixtures of convex tests. -/
lemma baseline_cost_eq_max (a B L T : ℚ) (hL : 0 ≤ L) :
    a * B + T + L * max (1 - B) 0 =
      max (a * B + T) (L + (a - L) * B + T) := by
  by_cases h : B ≤ 1
  · rw [max_eq_left (by linarith)]
    have hmul := mul_nonneg hL (show 0 ≤ 1 - B by linarith)
    rw [max_eq_right (by nlinarith)]
    ring
  · rw [max_eq_right (by linarith)]
    have hmul := mul_nonpos_of_nonneg_of_nonpos hL (show 1 - B ≤ 0 by linarith)
    rw [max_eq_left (by nlinarith)]
    ring

/-- Larger losses pair with smaller future baselines in the maximizing
uncrossing. Terms depending only on the baseline cancel from this inequality. -/
lemma baseline_loss_antimonge (B₀ B₁ L₀ L₁ : ℚ) (hB : B₀ ≤ B₁) (hL : L₀ ≤ L₁) :
    L₀ * max (1 - B₀) 0 + L₁ * max (1 - B₁) 0 ≤
      L₁ * max (1 - B₀) 0 + L₀ * max (1 - B₁) 0 := by
  have hh : max (1 - B₁) (0 : ℚ) ≤ max (1 - B₀) 0 :=
    max_le_max (by linarith) le_rfl
  have hmul := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hh)
  nlinarith

/-- Exact fiberwise thinning permits the signed baseline correction. The
increment comparison is still a separate, explicit hypothesis. -/
theorem fiber_exact_baseline_step {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ h B T : Ω → ℚ) (ν F : Ω → A → ℚ)
    (hmass : ∀ x, (∑ y, ν x y) = μ x * h x)
    (hfuture : (∑ x, ∑ y, ν x y) ≤ ∑ x, ∑ y, ν x y * F x y)
    (hcomparison : (∑ x, ∑ y, ν x y * (F x y - B x)) ≤ ∑ x, μ x * T x) :
    (∑ x, μ x) ≤ ∑ x, μ x * ((1 - h x) + h x * B x + T x) := by
  have hsplit : (∑ x, ∑ y, ν x y * F x y) =
      (∑ x, μ x * h x * B x) + ∑ x, ∑ y, ν x y * (F x y - B x) := by
    calc
      _ = ∑ x, ∑ y, (ν x y * B x + ν x y * (F x y - B x)) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul, hmass]
  have hmain := hfuture.trans (hsplit.le.trans (add_le_add le_rfl hcomparison))
  simp_rw [hmass] at hmain
  have heq : (∑ x, μ x * ((1 - h x) + h x * B x + T x)) =
      (∑ x, μ x) - (∑ x, μ x * h x) +
        (∑ x, μ x * h x * B x) + ∑ x, μ x * T x := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq]
  linarith

/-- Every nonnegative fiber measure can be thinned to any prescribed mass
between zero and its available mass. -/
theorem exists_fiber_thinning {Ω A : Type*} [Fintype A]
    (w : Ω → A → ℚ) (target : Ω → ℚ)
    (hw : ∀ x y, 0 ≤ w x y) (ht0 : ∀ x, 0 ≤ target x)
    (ht : ∀ x, target x ≤ ∑ y, w x y) :
    ∃ ν : Ω → A → ℚ,
      (∀ x y, 0 ≤ ν x y ∧ ν x y ≤ w x y) ∧
        (∀ x, (∑ y, ν x y) = target x) := by
  let total (x : Ω) : ℚ := ∑ y, w x y
  have htotal (x : Ω) : 0 ≤ total x := Finset.sum_nonneg (fun y _ => hw x y)
  refine ⟨fun x y => (target x / total x) * w x y, ?_, ?_⟩
  · intro x y
    constructor
    · exact mul_nonneg (div_nonneg (ht0 x) (htotal x)) (hw x y)
    · by_cases hz : total x = 0
      · simp only [hz, div_zero, zero_mul]
        exact hw x y
      · have hp : 0 < total x := lt_of_le_of_ne (htotal x) (Ne.symm hz)
        have hh : target x / total x ≤ 1 := (div_le_one hp).mpr (ht x)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (hw x y)
  · intro x
    rw [← Finset.mul_sum]
    change target x / total x * total x = target x
    by_cases hz : total x = 0
    · have ht' : target x = 0 := le_antisymm (by simpa [total, hz] using ht x) (ht0 x)
      simp [ht']
    · exact div_mul_cancel₀ (target x) hz

/-- The live cutoff guarantees both feasible retention and a nonnegative
coefficient of the old-coordinate baseline in the geometric compression. -/
theorem live_retention_bounds (p c k : ℚ) (hp : 1 < p) (hc0 : 0 ≤ c)
    (hcp : c ≤ p) (hk : k ≤ (p - 1) * (1 - 1 / p)) :
    let L := max (1 - c + c * k / (p - 1)) 0
    0 ≤ L ∧ L ≤ 1 - c / p ∧ 1 - L ≤ c * (1 - k / (p - 1)) := by
  dsimp
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p - 1 := by linarith
  have hk' : k / (p - 1) ≤ 1 - 1 / p := (div_le_iff₀ hq0).mpr (by simpa only [mul_comm] using hk)
  have hh := mul_le_mul_of_nonneg_left hk' hc0
  have he : c * (1 - 1 / p) = c - c / p := by ring
  rw [he] at hh
  have hr : 0 ≤ 1 - c / p := sub_nonneg.mpr ((div_le_one hp0).mpr hcp)
  refine ⟨le_max_right _ _, max_le ?_ hr, ?_⟩
  · calc
      1 - c + c * k / (p - 1) = 1 - c + c * (k / (p - 1)) := by ring
      _ ≤ 1 - c / p := by linarith
  · have hmax := le_max_left (1 - c + c * k / (p - 1)) (0 : ℚ)
    calc
      1 - max (1 - c + c * k / (p - 1)) 0 ≤ 1 - (1 - c + c * k / (p - 1)) := by linarith
      _ = c * (1 - k / (p - 1)) := by ring

lemma exact_loss_antimonge (B₀ B₁ L₀ L₁ : ℚ) (hB : B₀ ≤ B₁) (hL : L₀ ≤ L₁) :
    L₀ * (1 - B₀) + L₁ * (1 - B₁) ≤
      L₁ * (1 - B₀) + L₀ * (1 - B₁) := by
  have hh := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hB)
  nlinarith

#print axioms fiber_exact_baseline_step
#print axioms exists_fiber_thinning
#print axioms live_retention_bounds
#print axioms exact_loss_antimonge

#print axioms defect_baseline_bound
#print axioms fiber_baseline_step
#print axioms baseline_cost_eq_max
#print axioms baseline_loss_antimonge
end Erdos7BaselineRetention
