import Submission.TreeBasic

/-! Scalar efficiency bounds for mixed query trees.

The simultaneous induction keeps `f + z ≤ 1`, `g + z ≤ 2 * eta`, and
`f + z ≤ tau + g`.  These are equivalent to the useful difference
invariants, but make the nonnegative multipliers in the binary recurrence
explicit.  No matrix or probabilistic arguments are used.
-/

namespace ErdosDSS.TreeCode

namespace Efficiency

open Tree

noncomputable section

/-- The scalar induction invariant, also valid at leaves. -/
private structure MassBounds (t : Tree) : Prop where
  tau_nonneg : 0 ≤ t.tau
  tau_le_one : t.tau ≤ 1
  eta_nonneg : 0 ≤ t.eta
  eta_le_half : t.eta ≤ 1 / 2
  f_nonneg : 0 ≤ t.f
  z_nonneg : 0 ≤ t.z
  g_nonneg : 0 ≤ t.g
  f_add_z_le_one : t.f + t.z ≤ 1
  g_add_z_le_two_eta : t.g + t.z ≤ 2 * t.eta
  f_add_z_le_tau_add_g : t.f + t.z ≤ t.tau + t.g
  eta_le_tau : t.eta ≤ t.tau

private lemma leaf_bounds (a : Bool) : MassBounds (tip a) := by
  cases a <;> constructor <;> norm_num [tau, eta, f, z, g]

private lemma cherry_bounds (a b : Bool) (hab : a ≠ b) :
    MassBounds (fork (tip a) (tip b)) := by
  cases a <;> cases b <;> simp_all
  all_goals constructor <;> norm_num [tau, eta, f, z, g, isNode]

private lemma unary_left_bounds {l : Tree} (hl : MassBounds l)
    (hn : l.isNode = true) (a : Bool) : MassBounds (fork l (tip a)) := by
  have htip : (tip a).isNode = false := rfl
  rcases hl with ⟨ht0, ht1, he0, he1, hf0, hz0, hg0, hfz, hge, hft, het⟩
  cases a <;> constructor <;> simp [tau, eta, f, z, g, hn, htip] <;> linarith

private lemma unary_right_bounds (a : Bool) {r : Tree} (hr : MassBounds r)
    (hn : r.isNode = true) : MassBounds (fork (tip a) r) := by
  have htip : (tip a).isNode = false := rfl
  rcases hr with ⟨ht0, ht1, he0, he1, hf0, hz0, hg0, hfz, hge, hft, het⟩
  cases a <;> constructor <;> simp [tau, eta, f, z, g, hn, htip] <;> linarith

private lemma binary_bounds {l r : Tree} (hl : MassBounds l) (hr : MassBounds r)
    (hnl : l.isNode = true) (hnr : r.isNode = true) : MassBounds (fork l r) := by
  have hfactor : 0 ≤ 1 + r.z := by linarith [hr.z_nonneg]
  have hfz := mul_le_mul_of_nonneg_left hl.f_add_z_le_one hfactor
  have hge := mul_le_mul_of_nonneg_left hl.g_add_z_le_two_eta hfactor
  have hft := mul_le_mul_of_nonneg_left hl.f_add_z_le_tau_add_g hfactor
  have he := mul_le_mul_of_nonneg_left hl.eta_le_half hr.z_nonneg
  have ht := mul_le_mul_of_nonneg_left hl.tau_le_one hr.z_nonneg
  have hzf := mul_nonneg hr.z_nonneg hl.f_nonneg
  have hzz := mul_nonneg hl.z_nonneg hr.z_nonneg
  have hzg := mul_nonneg hr.z_nonneg hl.g_nonneg
  constructor <;> simp [tau, eta, f, z, g, hnl, hnr]
  · linarith only [hl.tau_nonneg, hr.tau_nonneg]
  · linarith only [hl.tau_le_one, hr.tau_le_one]
  · linarith only [hl.eta_nonneg, hr.eta_nonneg]
  · linarith only [hl.eta_le_half, hr.eta_le_half]
  · linarith only [hl.f_nonneg, hr.f_nonneg, hzf]
  · nlinarith only [hl.z_nonneg, hzz]
  · linarith only [hl.g_nonneg, hr.g_nonneg, hzg]
  · nlinarith only [hfz, hr.f_add_z_le_one]
  · nlinarith only [hge, he, hr.g_add_z_le_two_eta]
  · nlinarith only [hft, ht, hr.f_add_z_le_tau_add_g]
  · linarith only [hl.eta_le_tau, hr.eta_le_tau]

private theorem mixed_bounds {t : Tree} (ht : t.Mixed) : MassBounds t := by
  induction t with
  | tip a => exact leaf_bounds a
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := ht
    have hl := ihl hml
    have hr := ihr hmr
    cases l with
    | tip a =>
      cases r with
      | tip b =>
        exact cherry_bounds a b (hch rfl rfl)
      | fork rl rr =>
        exact unary_right_bounds a hr rfl
    | fork ll lr =>
      cases r with
      | tip b =>
        exact unary_left_bounds hl rfl b
      | fork rl rr =>
        exact binary_bounds hl hr rfl rfl

/-- All five scalar masses are nonnegative on a mixed tree. -/
theorem mass_nonneg {t : Tree} (ht : t.Mixed) :
    0 ≤ t.tau ∧ 0 ≤ t.eta ∧ 0 ≤ t.f ∧ 0 ≤ t.z ∧ 0 ≤ t.g := by
  have h := mixed_bounds ht
  exact ⟨h.tau_nonneg, h.eta_nonneg, h.f_nonneg, h.z_nonneg, h.g_nonneg⟩

/-- The conditional timeout mass is at most one. -/
theorem timeout_mass_le_one {t : Tree} (ht : t.Mixed) : t.tau ≤ 1 :=
  (mixed_bounds ht).tau_le_one

/-- Generic half bound for the cherry-timeout mass. -/
theorem cherry_mass_le_half {t : Tree} (ht : t.Mixed) : t.eta ≤ (1 / 2 : ℚ) :=
  (mixed_bounds ht).eta_le_half

/-- Cherry-timeout mass is part of the total timeout mass. -/
theorem cherry_mass_le_timeout {t : Tree} (ht : t.Mixed) : t.eta ≤ t.tau :=
  (mixed_bounds ht).eta_le_tau

/-- The transformed timeout and first-cherry masses fit in one unit. -/
theorem feedback_add_first_cherry_le_one {t : Tree} (ht : t.Mixed) : t.f + t.z ≤ 1 :=
  (mixed_bounds ht).f_add_z_le_one

/-- Difference invariant controlling the transformed cherry mass. -/
theorem cherry_difference_bound {t : Tree} (ht : t.Mixed) :
    t.g - t.eta ≤ (t.g - t.z) / 2 := by
  have h := (mixed_bounds ht).g_add_z_le_two_eta
  linarith

/-- Difference invariant controlling the extra feedback mass. -/
theorem feedback_difference_bound {t : Tree} (ht : t.Mixed) :
    t.f - t.tau ≤ t.g - t.z := by
  have h := (mixed_bounds ht).f_add_z_le_tau_add_g
  linarith

/-- The endpoint bound holds even at the mixed leaves. -/
theorem feedback_mass_bound_all {t : Tree} (ht : t.Mixed) :
    0 ≤ t.f ∧ t.f ≤ t.tau + 2 * t.eta := by
  have h := mixed_bounds ht
  refine ⟨h.f_nonneg, ?_⟩
  linarith [h.f_add_z_le_tau_add_g, h.g_add_z_le_two_eta, h.z_nonneg]

/-- Scalar efficiency endpoint for a mixed query tree. -/
theorem feedback_mass_bound {t : Tree} (ht : t.Mixed) (_hnode : t.isNode = true) :
    0 ≤ t.f ∧ t.f ≤ t.tau + 2 * t.eta :=
  feedback_mass_bound_all ht

/-- The feedback mass is at most three times the timeout mass. -/
theorem feedback_mass_le_three_tau {t : Tree} (ht : t.Mixed) : t.f ≤ 3 * t.tau := by
  linarith [(feedback_mass_bound_all ht).2, cherry_mass_le_timeout ht]

/-- A timeout bound supplied by the walk gives the `3/8` feedback bound. -/
theorem feedback_mass_le_three_eighths {t : Tree} (ht : t.Mixed)
    (hsmall : t.tau ≤ (1 / 8 : ℚ)) : t.f ≤ (3 / 8 : ℚ) := by
  linarith [feedback_mass_le_three_tau ht]

/-- The scalar period is normalized by the number of leaves, `nodes + 1`. -/
theorem scalar_period_normalized (t : Tree) :
    (2 : ℚ) ^ t.nodes * (1 + t.f) / (2 : ℚ) ^ (t.nodes + 1) = (1 + t.f) / 2 := by
  rw [pow_succ]
  field_simp

/-- The unadjusted normalized scalar period is at most `11/16`. -/
theorem scalar_period_ratio_le_eleven_sixteenths {t : Tree} (ht : t.Mixed)
    (hsmall : t.tau ≤ (1 / 8 : ℚ)) :
    (2 : ℚ) ^ t.nodes * (1 + t.f) / (2 : ℚ) ^ (t.nodes + 1) ≤ (11 / 16 : ℚ) := by
  rw [scalar_period_normalized]
  linarith [feedback_mass_le_three_eighths ht hsmall]

/-- The `11/16` bound leaves strict slack below `17/24`. -/
theorem scalar_period_ratio_lt_seventeen_twentyfourths {t : Tree} (ht : t.Mixed)
    (hsmall : t.tau ≤ (1 / 8 : ℚ)) :
    (2 : ℚ) ^ t.nodes * (1 + t.f) / (2 : ℚ) ^ (t.nodes + 1) < (17 / 24 : ℚ) := by
  exact lt_of_le_of_lt (scalar_period_ratio_le_eleven_sixteenths ht hsmall) (by norm_num)

/-- Downstream efficiency arithmetic, without any determinant hypotheses. -/
theorem scalar_period_efficiency {t : Tree} (ht : t.Mixed)
    (hsmall : t.tau ≤ (1 / 8 : ℚ)) :
    24 * ((2 : ℚ) ^ t.nodes * (1 + t.f)) ≤ 17 * (2 : ℚ) ^ (t.nodes + 1) := by
  have hp : 0 ≤ (2 : ℚ) ^ t.nodes := by positivity
  have hb := mul_le_mul_of_nonneg_left (feedback_mass_le_three_eighths ht hsmall) hp
  rw [pow_succ]
  nlinarith only [hb, hp]

/-- Apply the scalar estimate to any natural period with the stated formula. -/
theorem period_efficiency_of_eq {t : Tree} (ht : t.Mixed)
    (hsmall : t.tau ≤ (1 / 8 : ℚ)) {B : ℕ}
    (hB : (B : ℚ) = (2 : ℚ) ^ t.nodes * (1 + t.f)) :
    24 * B ≤ 17 * 2 ^ (t.nodes + 1) := by
  have h : (24 : ℚ) * (B : ℚ) ≤ 17 * (2 : ℚ) ^ (t.nodes + 1) := by
    rw [hB]
    exact scalar_period_efficiency ht hsmall
  exact_mod_cast h

end

end Efficiency

end ErdosDSS.TreeCode
