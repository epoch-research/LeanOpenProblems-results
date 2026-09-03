import FormalConjecturesUtil

/-! Ordered coefficient rows for exact retention, including an earlier kill cutoff. -/
namespace Erdos7RetentionRows
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- The live cutoff guarantees both feasible retention and a nonnegative
coefficient of the old-coordinate baseline in the geometric compression. -/
theorem live_retention_bounds (p c k : ℝ) (hp : 1 < p) (hc0 : 0 ≤ c)
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
  · have hmax := le_max_left (1 - c + c * k / (p - 1)) (0 : ℝ)
    calc
      1 - max (1 - c + c * k / (p - 1)) 0 ≤ 1 - (1 - c + c * k / (p - 1)) := by linarith
      _ = c * (1 - k / (p - 1)) := by ring

noncomputable def liveLoss (p c k : ℝ) : ℝ := max (1-c+c*k/(p-1)) 0
noncomputable def loss (p c K k : ℝ) : ℝ := if k ≤ K then liveLoss p c k else 1
noncomputable def baseline (p c K k : ℝ) : ℝ := if k ≤ K then 1-liveLoss p c k-c/p else 0
noncomputable def density (c K k : ℝ) : ℝ := if k ≤ K then c else 0

lemma liveLoss_monotone (p c : ℝ) (hp : 1 < p) (hc : 0 ≤ c) :
    Monotone (liveLoss p c) := by
  intro k l hkl
  apply max_le_max _ le_rfl
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkl hc)
    (show 0 ≤ p-1 by linarith)
  linarith

lemma loss_bounds (p c K k : ℝ) (hp : 1 < p) (hc : 0 ≤ c) (hcp : c ≤ p)
    (hK : K ≤ (p-1)*(1-1/p)) : 0 ≤ loss p c K k ∧ loss p c K k ≤ 1 := by
  by_cases hk : k ≤ K
  · have hh := live_retention_bounds p c k hp hc hcp (hk.trans hK)
    have hd : 0 ≤ c/p := div_nonneg hc (by linarith)
    simp only [loss, if_pos hk, liveLoss]
    exact ⟨hh.1, by linarith [hh.2.1]⟩
  · simp [loss, hk]

lemma baseline_nonneg (p c K k : ℝ) (hp : 1 < p) (hc : 0 ≤ c) (hcp : c ≤ p)
    (hK : K ≤ (p-1)*(1-1/p)) : 0 ≤ baseline p c K k := by
  by_cases hk : k ≤ K
  · have hh := live_retention_bounds p c k hp hc hcp (hk.trans hK)
    simp only [baseline, if_pos hk, liveLoss]
    linarith [hh.2.1]
  · simp [baseline, hk]

lemma density_nonneg (c K k : ℝ) (hc : 0 ≤ c) : 0 ≤ density c K k := by
  simp only [density]
  split_ifs <;> positivity

lemma loss_monotone (p c K : ℝ) (hp : 1 < p) (hc : 0 ≤ c) (hcp : c ≤ p)
    (hK : K ≤ (p-1)*(1-1/p)) : Monotone (loss p c K) := by
  intro k l hkl
  by_cases hl : l ≤ K
  · simp only [loss, if_pos hl, if_pos (hkl.trans hl)]
    exact liveLoss_monotone p c hp hc hkl
  · simp only [loss, if_neg hl]
    exact (loss_bounds p c K k hp hc hcp hK).2

lemma baseline_antitone (p c K : ℝ) (hp : 1 < p) (hc : 0 ≤ c) (hcp : c ≤ p)
    (hK : K ≤ (p-1)*(1-1/p)) : Antitone (baseline p c K) := by
  intro k l hkl
  by_cases hl : l ≤ K
  · simp only [baseline, if_pos hl, if_pos (hkl.trans hl)]
    have hh := liveLoss_monotone p c hp hc hkl
    linarith
  · simp only [baseline, if_neg hl]
    exact baseline_nonneg p c K k hp hc hcp hK

lemma density_antitone (c K : ℝ) (hc : 0 ≤ c) : Antitone (density c K) := by
  intro k l hkl
  by_cases hl : l ≤ K
  · simp only [density, if_pos hl, if_pos (hkl.trans hl), le_refl]
  · simp only [density, if_neg hl]
    exact density_nonneg c K k hc

/-- Reversing any finite list of actual counts yields the ordered rows needed
by the dual-splitting theorem. The kill cutoff may be strictly earlier than
the maximal cutoff imposed by positivity of the baseline. -/
theorem reversed_rows_ordered {ι : Type*} (p c K : ℝ)
    (hp : 1 < p) (hc : 0 ≤ c) (hcp : c ≤ p) (hK : K ≤ (p-1)*(1-1/p))
    (k : ℕ → ℝ) (hk : Antitone k) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    Monotone (fun r => baseline p c K (k r)) ∧
    (∀ i, Monotone (fun r => density c K (k r)*q i)) := by
  refine ⟨(baseline_antitone p c K hp hc hcp hK).comp hk, ?_⟩
  intro i r s hrs
  exact mul_le_mul_of_nonneg_right (density_antitone c K hc (hk hrs)) (hq i)

#print axioms reversed_rows_ordered
end Erdos7RetentionRows
