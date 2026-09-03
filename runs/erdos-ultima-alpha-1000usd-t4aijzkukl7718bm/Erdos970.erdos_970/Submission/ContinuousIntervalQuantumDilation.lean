import Submission.ContinuousIntervalQuantumIteration
import Submission.ContinuousIntervalQuantumGain
import Submission.ContinuousIntervalDilation

/-! A multiplicative length budget for repeated quantum refinements. No boundedness
of this budget independent of the number of stages, and no quadratic positivity,
is assumed or asserted. There are no later chord patches in this comparison. -/
namespace Erdos970.ContinuousInterval

lemma Regular.dilation_self {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (c : ℝ) (hc : 1 ≤ c) :
    Dominates (fun x => L (c * x) / c) (fun x => U (c * x) / c) L U := by
  have hc0 : 0 < c := by linarith
  have hi0 : 0 ≤ 1 / c := by positivity
  have hi1 : 1 / c ≤ 1 := (div_le_one hc0).mpr hc
  have he (x : ℝ) : (1 / c) * (c * x) + (1 - 1 / c) * 0 = x := by
    field_simp
    ring
  have hL0 := h.lower_zero 0 le_rfl
  constructor
  · intro x
    have hh := h.lower_convex.2 (Set.mem_univ (c * x)) (Set.mem_univ (0 : ℝ))
      hi0 (sub_nonneg.mpr hi1) (show 1 / c + (1 - 1 / c) = 1 by ring)
    simp only [smul_eq_mul] at hh
    rw [he] at hh
    simpa only [hL0, mul_zero, zero_mul, add_zero, one_div, div_eq_mul_inv, mul_comm, mul_one] using hh
  · intro x hx
    have hh := h.upper_concave.2 (show 0 ≤ c * x by positivity) (show (0 : ℝ) ≤ 0 by rfl)
      hi0 (sub_nonneg.mpr hi1) (show 1 / c + (1 - 1 / c) = 1 by ring)
    simp only [smul_eq_mul] at hh
    rw [he] at hh
    simpa only [h.upper_zero, mul_zero, zero_mul, add_zero, one_div, div_eq_mul_inv, mul_comm, mul_one] using hh

lemma Dominates.dilate {L U L' U' : ℝ → ℝ} (h : Dominates L U L' U')
    (c : ℝ) (hc : 0 < c) :
    Dominates (fun x => L (c * x) / c) (fun x => U (c * x) / c)
      (fun x => L' (c * x) / c) (fun x => U' (c * x) / c) := by
  exact ⟨fun x => div_le_div_of_nonneg_right (h.1 _) hc.le,
    fun x hx => div_le_div_of_nonneg_right (h.2 _ (mul_nonneg hc.le hx)) hc.le⟩

/-- The chord beyond `g+1` dominates the new affine support after this dilation. -/
theorem Regular.quantumPatch_dilation {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g : ℕ) (hd : 0 < d) (hg : 0 < g)
    (hz : L ((g - 1 : ℕ) : ℝ) = 0) (c : ℝ) (hc : 1 ≤ c)
    (hcg : (g : ℝ) + 1 ≤ c * ((g : ℝ) - 1)) :
    Dominates (fun x => L (c * x) / c) (fun x => U (c * x) / c)
      (ContinuousInterval.quantumPatch d g (quantumSlope L g) (quantumIntercept L g) L) U := by
  have hc0 : 0 < c := by linarith
  have hself := h.dilation_self c hc
  have hs := h.quantumSlope_bounds g
  have ha := h.quantumIntercept_nonpos g hg hz
  let l := L (g : ℝ)
  let s := quantumSlope L g
  let b := quantumFactor d (l - s) * s
  have hl : 0 ≤ l := h.lower_nonneg _
  have hls : l ≤ s := by change l - s ≤ 0 at ha; linarith
  have hb := quantum_adjusted_slope_bounds hd hl hls hs.2
  change l ≤ b ∧ b ≤ s ∧ b - l ≤ d / 2 at hb
  refine ⟨?_, hself.2⟩
  intro x
  change max (L x) (b * (x - ((g : ℝ) - 1))) ≤ L (c * x) / c
  refine max_le (hself.1 x) ?_
  by_cases hx : x ≤ (g : ℝ) - 1
  · exact (mul_nonpos_of_nonneg_of_nonpos (hl.trans hb.1) (sub_nonpos.mpr hx)).trans
      (div_nonneg (h.lower_nonneg _) hc0.le)
  · have hxc : (g : ℝ) + 1 ≤ c * x := by
      nlinarith [mul_nonneg hc0.le (show 0 ≤ x - ((g : ℝ) - 1) by linarith)]
    have hch := chord_le_outside h.lower_convex (g : ℝ) (c * x)
      (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) (Or.inr hxc)
    change l + (c * x - (g : ℝ)) * s ≤ L (c * x) at hch
    apply (le_div_iff₀ hc0).mpr
    have h1 := mul_nonneg (show 0 ≤ s - b by linarith [hb.2.1])
      (mul_nonneg hc0.le (show 0 ≤ x - ((g : ℝ) - 1) by linarith))
    have h2 := mul_nonneg hs.1 (show 0 ≤ c * ((g : ℝ) - 1) - g by linarith)
    nlinarith

noncomputable def quantumDilationFactor (g : ℕ) : ℝ :=
  ((g : ℝ) + 1) / ((g : ℝ) - 1)

lemma quantumDilationFactor_one_le {g : ℕ} (hg : 1 < g) :
    1 ≤ quantumDilationFactor g := by
  have hgR : (1 : ℝ) < g := by exact_mod_cast hg
  unfold quantumDilationFactor
  apply (le_div_iff₀ (by linarith)).mpr
  linarith

lemma quantumDilationFactor_identity {g : ℕ} (hg : 1 < g) :
    quantumDilationFactor g * ((g : ℝ) - 1) = (g : ℝ) + 1 := by
  have hne : (g : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < g := by exact_mod_cast hg
    linarith
  exact div_mul_cancel₀ _ hne

/-- A failed guard requires no extra argument; a successful guard permits the
single-patch comparison. This lemma assumes only that the supplied trigger exceeds one. -/
theorem Regular.quantumRefine_dilation {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g : ℕ) (hg : 1 < g) :
    Dominates (fun x => L (quantumDilationFactor g * x) / quantumDilationFactor g)
      (fun x => U (quantumDilationFactor g * x) / quantumDilationFactor g)
      (ContinuousInterval.quantumRefine d g L) U := by
  unfold ContinuousInterval.quantumRefine
  split_ifs with hh
  · exact h.quantumPatch_dilation g hh.1 hh.2.1 hh.2.2.1 _
      (quantumDilationFactor_one_le hg) (quantumDilationFactor_identity hg).ge
  · exact h.dilation_self _ (quantumDilationFactor_one_le hg)

noncomputable def quantumDilationBudget (trigger : ℕ → ℕ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, quantumDilationFactor (trigger i)

lemma quantumDilationBudget_one_le (trigger : ℕ → ℕ) (k : ℕ)
    (ht : ∀ i < k, 1 < trigger i) : 1 ≤ quantumDilationBudget trigger k := by
  calc
    1 = ∏ _i ∈ Finset.range k, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num)
      (fun i hi => quantumDilationFactor_one_le (ht i (Finset.mem_range.mp hi)))

/-- All later quantum refinements are accounted for by an explicit PRODUCT
of length factors. This has no hypothesis or conclusion of uniform positivity. -/
theorem quantumEnvelope_dilation_budget (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) (ht : ∀ i < k, 1 < trigger i) :
    Dominates (fun x => (envelope Q k (quantumDilationBudget trigger k * x)).1 /
        quantumDilationBudget trigger k)
      (fun x => (envelope Q k (quantumDilationBudget trigger k * x)).2 /
        quantumDilationBudget trigger k)
      (quantumEnvelope Q (fun _ => []) trigger k).1
      (quantumEnvelope Q (fun _ => []) trigger k).2 := by
  induction k with
  | zero =>
    constructor <;> intros <;> simp [quantumDilationBudget, envelope, quantumEnvelope]
  | succ k ih =>
    have hQQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    have htt : ∀ i < k, 1 < trigger i := fun i hi => ht i (by omega)
    have hqk := hQ k (by omega)
    have htk := ht k (by omega)
    have hd := quantumDilationBudget_one_le trigger k htt
    have hc := quantumDilationFactor_one_le htk
    have hc0 : 0 < quantumDilationFactor (trigger k) := by linarith
    let E := quantumEnvelope Q (fun _ => []) trigger k
    let A := stepLower (Q k) E.1 E.2
    let B := stepUpper (Q k) E.1 E.2
    have hstep := (ih hQQ htt).step (Q k) hqk.1 hqk.2
    have hscale := (envelope_regular Q k hQQ).dilation_step (Q k)
      (quantumDilationBudget trigger k) hqk.1 hqk.2 hd
    have hpre := (hscale.trans hstep).dilate (quantumDilationFactor (trigger k)) hc0
    have hreg := (quantumEnvelope_regular Q (fun _ => []) trigger k hQQ).step
      (Q k) hqk.1 hqk.2
    have he : density Q k * (1 - Q k) = density Q (k + 1) := by
      simp only [density, Finset.prod_range_succ]
    rw [he] at hreg
    have hpatch := hreg.quantumRefine_dilation (trigger k) htk
    have hall := hpre.trans hpatch
    have hbudget : quantumDilationBudget trigger (k + 1) =
        quantumDilationBudget trigger k * quantumDilationFactor (trigger k) := by
      simp only [quantumDilationBudget, Finset.prod_range_succ]
    simpa only [quantumEnvelope, chordPatches, hbudget, envelope, E, A, B,
      mul_assoc, div_div] using hall

lemma quantumDilationFactor_eq_one_add {g : ℕ} (hg : 1 < g) :
    quantumDilationFactor g = 1 + 2 / ((g : ℝ) - 1) := by
  have hne : (g : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < g := by exact_mod_cast hg
    linarith
  unfold quantumDilationFactor
  field_simp
  ring

/-- A finite reciprocal-trigger sum controls the full multiplicative budget. -/
theorem quantumDilationBudget_le_exp (trigger : ℕ → ℕ) (k : ℕ)
    (ht : ∀ i < k, 1 < trigger i) :
    quantumDilationBudget trigger k ≤
      Real.exp (∑ i ∈ Finset.range k, 2 / ((trigger i : ℝ) - 1)) := by
  induction k with
  | zero => simp [quantumDilationBudget]
  | succ k ih =>
    have htt : ∀ i < k, 1 < trigger i := fun i hi => ht i (by omega)
    have htk := ht k (by omega)
    have hc : quantumDilationFactor (trigger k) ≤
        Real.exp (2 / ((trigger k : ℝ) - 1)) := by
      rw [quantumDilationFactor_eq_one_add htk]
      simpa only [add_comm] using Real.add_one_le_exp (2 / ((trigger k : ℝ) - 1))
    rw [quantumDilationBudget, Finset.prod_range_succ,
      Finset.sum_range_succ, Real.exp_add]
    exact mul_le_mul (ih htt) hc (by linarith [quantumDilationFactor_one_le htk])
      (Real.exp_pos _).le

lemma quantumDilationFactor_le_of_index {i g : ℕ} (hg : i + 2 ≤ g) :
    quantumDilationFactor g ≤ ((i : ℝ) + 3) / ((i : ℝ) + 1) := by
  have hgR : (i : ℝ) + 2 ≤ g := by exact_mod_cast hg
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hden : 0 < (g : ℝ) - 1 := by linarith
  unfold quantumDilationFactor
  apply (div_le_div_iff₀ hden (by positivity)).mpr
  nlinarith

/-- If triggers are at least stage number plus one, the accumulated length
budget is at most quadratic, rather than the exponential additive-error bound. -/
theorem quantumDilationBudget_le_polynomial (trigger : ℕ → ℕ) (k : ℕ)
    (ht : ∀ i < k, i + 2 ≤ trigger i) :
    quantumDilationBudget trigger k ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  induction k with
  | zero => simp [quantumDilationBudget]
  | succ k ih =>
    have htt : ∀ i < k, i + 2 ≤ trigger i := fun i hi => ht i (by omega)
    have htk := ht k (by omega)
    have hc := quantumDilationFactor_le_of_index htk
    have hc0 : 0 ≤ quantumDilationFactor (trigger k) := by
      have := quantumDilationFactor_one_le (show 1 < trigger k by omega)
      linarith
    have hm := mul_le_mul (ih htt) hc hc0 (by positivity :
      0 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2)
    have he : (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) *
        (((k : ℝ) + 3) / ((k : ℝ) + 1)) =
        (((k + 1 : ℕ) : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) + 2) / 2 := by
      push_cast
      field_simp
      ring
    rw [he] at hm
    simpa only [quantumDilationBudget, Finset.prod_range_succ] using hm

/-- This implication transfers positivity back to the ORIGINAL recurrence,
with the explicitly enlarged real length. It does not establish its premise. -/
theorem envelope_positive_of_quantum_positive (Q : ℕ → ℝ) (trigger : ℕ → ℕ)
    (k : ℕ) (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1)
    (ht : ∀ i < k, 1 < trigger i) (x : ℝ)
    (hpos : 0 < (quantumEnvelope Q (fun _ => []) trigger k).1 x) :
    0 < (envelope Q k (quantumDilationBudget trigger k * x)).1 := by
  have hh := hpos.trans_le ((quantumEnvelope_dilation_budget Q trigger k hQ ht).1 x)
  have hd : 0 < quantumDilationBudget trigger k := by
    linarith [quantumDilationBudget_one_le trigger k ht]
  exact (div_pos_iff.mp hh).resolve_right (by intro h; linarith [h.2]) |>.1

#print axioms quantumDilationBudget_le_exp
#print axioms quantumDilationBudget_le_polynomial
#print axioms envelope_positive_of_quantum_positive

#print axioms Regular.quantumPatch_dilation
#print axioms quantumEnvelope_dilation_budget
end Erdos970.ContinuousInterval
