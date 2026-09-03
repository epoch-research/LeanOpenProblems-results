import Submission.LocalizedPatternCriterion

/-! Geometric support and boundary control for local configurations. Local
polynomial identities may only be applied when all their vertices remain in
the domain; the discarded boundary mass is bounded explicitly. -/
namespace Erdos3BohrPatternGeometry
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3RelativeStableBohr
  Erdos3BohrTranslation Erdos3CorrelationSifting Erdos3CrootSisaskL2
  Erdos3RobustTopDegreeCounting Erdos3BohrLocalAverages
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma bohr_nsmul {C : Finset (AddChar G ℂ)} {r : ℝ} {x : G}
    (hx : x ∈ bohr C r) (n : ℕ) : n • x ∈ bohr C ((n : ℝ)*r) := by
  induction n with
  | zero => simpa only [zero_nsmul,Nat.cast_zero,zero_mul] using bohr_zero C (le_refl 0)
  | succ n ih =>
    have h := bohr_add ih hx
    simpa only [add_nsmul,one_nsmul,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

/-- Choosing steps from B-B, where B has radius h/(2k), keeps every first-k
progression shift inside the Bohr set of radius h. -/
lemma small_difference_shifts (C : Finset (AddChar G ℂ)) {h : ℝ} (hh : 0 ≤ h)
    {k : ℕ} (hk : 0 < k) {b c : G}
    (hb : b ∈ bohr C (h/(2*(k : ℝ)))) (hc : c ∈ bohr C (h/(2*(k : ℝ))))
    (i : Fin k) : i.val • (c-b) ∈ bohr C h := by
  have hd : c-b ∈ bohr C (2*(h/(2*(k : ℝ)))) := by
    simpa only [sub_eq_add_neg,two_mul] using bohr_add hc (bohr_neg hb)
  apply bohr_mono C _ (bohr_nsmul hd i.val)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have he : (k : ℝ)*(2*(h/(2*(k : ℝ)))) = h := by field_simp
  calc
    _ ≤ (k : ℝ)*(2*(h/(2*(k : ℝ)))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast i.isLt.le
    _ = h := he

lemma shifted_exit_mass_le (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    {s : G} (hs : s ∈ bohr C (relativeWidth C z r)) :
    (𝔼 t : bohr C r, (1-indicator (bohr C r) (t+s))) ≤ 1/(z : ℝ) := by
  let W := bohr C r
  letI : Nonempty W := ⟨⟨0,bohr_zero C hr.le⟩⟩
  have h := smooth_bohr_translation_le C hr.le (relativeWidth_pos C hz hr).le
    (by positivity : (0 : ℝ) ≤ 1/z) (by norm_num : (0 : ℝ) ≤ 1) hstable
    (indicator W) (indicator_abs_le_one W) hs 0
  have h0 : smooth W (indicator W) 0 = 1 := by
    have he (t : W) : indicator W (0+t) = 1 := by simp only [zero_add,indicator,if_pos t.property]
    simp only [smooth,he,Fintype.expect_const]
  change |smooth W (indicator W) (0+s)-smooth W (indicator W) 0| ≤ (1/(z : ℝ))*1 at h
  rw [zero_add,h0,mul_one] at h
  have hswap : smooth W (indicator W) s = 𝔼 t : W, indicator W (t+s) := by
    unfold smooth
    simp only [add_comm s]
  rw [hswap] at h
  change (𝔼 t : W, (1-indicator W (t+s))) ≤ _
  rw [expect_sub_distrib,Fintype.expect_const]
  linarith [(abs_le.mp h).1]

variable {I : Type*} [Fintype I]

noncomputable def interiorMask (W : Finset G) (s : I → G) (t : G) : ℝ :=
  ∏ i : I, indicator W (t+s i)

lemma interiorMask_bounds (W : Finset G) (s : I → G) (t : G) :
    0 ≤ interiorMask W s t ∧ interiorMask W s t ≤ 1 := by
  constructor
  · exact prod_nonneg (fun i _ ↦ indicator_nonneg W _)
  · exact prod_le_one (fun i _ ↦ indicator_nonneg W _)
      (fun i _ ↦ by unfold indicator; split_ifs <;> norm_num)

lemma interiorMask_eq_one_iff (W : Finset G) (s : I → G) (t : G) :
    interiorMask W s t = 1 ↔ ∀ i, t+s i ∈ W := by
  simp only [interiorMask,indicator,Fintype.prod_boole]
  split_ifs with h
  · exact ⟨fun _ ↦ h,fun _ ↦ rfl⟩
  · exact ⟨fun h0 ↦ (zero_ne_one h0).elim,fun hn ↦ (h hn).elim⟩

/-- The probability of at least one vertex leaving the quadraticity domain
is at most the number of vertices times the stability tolerance. -/
theorem boundary_mass_le (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : I → G) (hs : ∀ i, s i ∈ bohr C (relativeWidth C z r)) :
    (𝔼 t : bohr C r, (1-interiorMask (bohr C r) s t)) ≤
      (Fintype.card I : ℝ)/(z : ℝ) := by
  have hpoint (t : bohr C r) : 1-interiorMask (bohr C r) s t ≤
      ∑ i : I, (1-indicator (bohr C r) (t+s i)) := by
    have h := abs_prod_sub_prod_le univ (fun _i : I ↦ (1 : ℝ))
      (fun i ↦ indicator (bohr C r) (t+s i)) (fun _ _ ↦ by norm_num)
      (fun i _ ↦ indicator_abs_le_one _ _)
    simp only [prod_const_one] at h
    change |1-interiorMask (bohr C r) s t| ≤ _ at h
    rw [abs_of_nonneg (sub_nonneg.mpr (interiorMask_bounds _ s t).2)] at h
    have he (i : I) : |1-indicator (bohr C r) (t+s i)| = 1-indicator (bohr C r) (t+s i) := by
      apply abs_of_nonneg
      have hi := indicator_abs_le_one (bohr C r) (t+s i)
      linarith [(abs_le.mp hi).2]
    simpa only [he] using h
  calc
    _ ≤ 𝔼 t : bohr C r, ∑ i : I, (1-indicator (bohr C r) (t+s i)) :=
      expect_le_expect (fun t _ ↦ hpoint t)
    _ = ∑ i : I, 𝔼 t : bohr C r, (1-indicator (bohr C r) (t+s i)) := expect_sum_comm _ _ _
    _ ≤ ∑ _i : I, 1/(z : ℝ) := sum_le_sum (fun i _ ↦ shifted_exit_mass_le C hr hz hstable (hs i))
    _ = _ := by simp [div_eq_mul_inv]

/-- Discarding boundary configurations changes the average of a unit-bounded
integrand by at most the same explicit boundary mass. -/
theorem mask_boundary_error (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : I → G) (hs : ∀ i, s i ∈ bohr C (relativeWidth C z r))
    (H : G → ℝ) (hH : ∀ t, |H t| ≤ 1) :
    |(𝔼 t : bohr C r, H t)-(𝔼 t : bohr C r, interiorMask (bohr C r) s t*H t)| ≤
      (Fintype.card I : ℝ)/(z : ℝ) := by
  rw [← expect_sub_distrib]
  have he (t : G) : H t-interiorMask (bohr C r) s t*H t =
      (1-interiorMask (bohr C r) s t)*H t := by ring
  simp only [he]
  apply (Finset.abs_expect_le _ _).trans
  apply le_trans _ (boundary_mass_le C hr hz hstable s hs)
  apply expect_le_expect
  intro t _
  rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (interiorMask_bounds _ _ _).2)]
  exact (mul_le_mul_of_nonneg_left (hH t)
    (sub_nonneg.mpr (interiorMask_bounds _ _ _).2)).trans_eq (mul_one _)

#print axioms small_difference_shifts
#print axioms boundary_mass_le
#print axioms mask_boundary_error
end Erdos3BohrPatternGeometry
