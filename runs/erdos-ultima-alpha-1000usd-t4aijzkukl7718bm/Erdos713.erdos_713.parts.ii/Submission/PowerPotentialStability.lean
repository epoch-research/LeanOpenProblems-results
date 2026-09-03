import FormalConjecturesUtil

/-! Stability of the unique maximum of a subquadratic pure-power potential.
This file contains only real analysis, not graph-exponent rationality. -/
open Filter Set
open scoped Topology
namespace Erdos713PowerPotential
set_option maxHeartbeats 1000000

noncomputable def phi (α c t : ℝ) : ℝ := c * t ^ α - c * α / 2 * t ^ 2

lemma rpow_square_half {α t : ℝ} (ht : 0 ≤ t) : (t ^ 2) ^ (α / 2) = t ^ α := by
  rw [← Real.rpow_two, ← Real.rpow_mul ht]
  congr 1
  ring

lemma phi_le {α c t : ℝ} (ha : 0 ≤ α) (ha2 : α ≤ 2) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    phi α c t ≤ c * (1 - α / 2) := by
  have h := rpow_one_add_le_one_add_mul_self (s := t^2-1) (by nlinarith : -1 ≤ t^2-1)
    (by linarith : 0 ≤ α/2) (by linarith : α/2 ≤ 1)
  rw [show 1 + (t^2-1) = t^2 by ring, rpow_square_half ht] at h
  have hh := mul_le_mul_of_nonneg_left h hc
  unfold phi
  nlinarith only [hh]

lemma phi_lt {α c t : ℝ} (ha : 0 < α) (ha2 : α < 2) (hc : 0 < c) (ht : 0 ≤ t)
    (hne : t ≠ 1) : phi α c t < c * (1 - α / 2) := by
  have h := rpow_one_add_lt_one_add_mul_self (s := t^2-1) (by nlinarith : -1 ≤ t^2-1)
    (by intro h; apply hne; nlinarith : t^2-1 ≠ 0) (by linarith : 0 < α/2) (by linarith : α/2 < 1)
  rw [show 1 + (t^2-1) = t^2 by ring, rpow_square_half ht] at h
  have hh := mul_lt_mul_of_pos_left h hc
  unfold phi
  nlinarith only [hh]

lemma continuous_phi {α c : ℝ} (ha : 0 < α) : Continuous (phi α c) := by
  have ha0 : 0 ≤ α := ha.le
  unfold phi
  fun_prop (disch := positivity)

lemma tail_bound {α c : ℝ} (ha2 : α < 2) (hc : 0 < c) (ha : 0 < α) :
    ∀ᶠ t : ℝ in atTop, (c+1) * t ^ α - c*α/2*t^2 ≤ -1 := by
  let C := c*α/2
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall : Tendsto (fun t : ℝ => (c+1)*t^(α-2)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (show 0 < 2-α by linarith)).const_mul (c+1)
  have hlarge : Tendsto (fun t : ℝ => C/2*t^2) atTop atTop := by
    exact (tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop (by positivity)
  filter_upwards [hsmall.eventually_lt_const (show 0 < C/2 by positivity),
    hlarge.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)] with t ht hl htp
  rw [Real.rpow_sub htp, Real.rpow_two] at ht
  have hq : (c+1)*t^α < C/2*t^2 := by
    have hd : ((c+1)*t^α)/t^2 < C/2 := by simpa only [mul_div_assoc] using ht
    have hh := (div_lt_iff₀ (sq_pos_of_pos htp)).mp hd
    exact hh
  change (c+1)*t^α-C*t^2 ≤ -1
  linarith

/-- Uniform stability permits an error in the leading coefficient as well
as an error in the objective value. The perturbation bound is uniform for
all nonnegative candidate orders. -/
theorem stable_maximum {α c ε : ℝ} (ha : 0 < α) (ha2 : α < 2) (hc : 0 < c)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 ≤ t →
      c*(1-α/2)-δ ≤ (c+δ)*t^α-c*α/2*t^2 → |t-1| < ε := by
  classical
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (tail_bound ha2 hc ha)
  let R := max R0 1
  have hR : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := by linarith
  let S : Set ℝ := Icc 0 R ∩ {t | ε ≤ |t-1|}
  have hS : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hS0 : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl,hRpos.le⟩,?_⟩
    simpa using hε1
  obtain ⟨u,hu,hmax⟩ := hS.exists_isMaxOn ⟨0,hS0⟩ (continuous_phi (c := c) ha).continuousOn
  have hune : u ≠ 1 := by
    intro hu1
    have hh := hu.2
    change ε ≤ |u-1| at hh
    rw [hu1, sub_self, abs_zero] at hh
    linarith
  have hgap : 0 < c*(1-α/2)-phi α c u := sub_pos.mpr (phi_lt ha ha2 hc hu.1.1 hune)
  let B := 1 + R^α
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := min 1 ((c*(1-α/2)-phi α c u)/(2*B))
  have hd : 0 < δ := lt_min (by norm_num) (div_pos hgap (by positivity))
  have hd1 : δ ≤ 1 := min_le_left _ _
  have hdB : δ*B ≤ (c*(1-α/2)-phi α c u)/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*B by positivity)).mp
      (min_le_right 1 ((c*(1-α/2)-phi α c u)/(2*B)))
    change δ*(2*B) ≤ _ at hh
    linarith
  refine ⟨δ,hd,hd1,?_⟩
  intro t ht hnear
  by_contra hbad
  have heps : ε ≤ |t-1| := le_of_not_gt hbad
  by_cases htR : t ≤ R
  · have hmem : t ∈ S := ⟨⟨ht,htR⟩,heps⟩
    have hmax' : phi α c t ≤ phi α c u := hmax hmem
    have hpow := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht htR ha.le) hd.le
    have hδ : δ*(1+R^α) ≤ (c*(1-α/2)-phi α c u)/2 := hdB
    unfold phi at hmax' hδ hgap
    nlinarith only [hnear,hmax',hpow,hδ,hgap]
  · have htail := hR0 t ((le_max_left R0 1).trans (le_of_not_ge htR))
    have hpow := mul_le_mul_of_nonneg_right hd1 (Real.rpow_nonneg ht α)
    have hM : 0 < c*(1-α/2) := mul_pos hc (by linarith)
    nlinarith only [hnear,htail,hpow,hd1,hM]

#print axioms phi_le
#print axioms phi_lt
#print axioms stable_maximum
end Erdos713PowerPotential
