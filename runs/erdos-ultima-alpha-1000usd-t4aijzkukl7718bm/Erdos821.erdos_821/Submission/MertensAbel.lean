import Submission.MertensPrimeLog

/-!
# Abel summation with a bounded prime-logarithm error

The elementary kernel used to pass from log(p)/p to 1/p is treated on
intervals bounded away from one. All errors are kept at both endpoints.
-/
open Nat Finset Filter ArithmeticFunction MeasureTheory
open scoped Classical BigOperators Topology
namespace Erdos821
set_option maxHeartbeats 3000000

noncomputable def mertensKernel (x : ℝ) : ℝ := 1/(x*(Real.log x)^2)

lemma hasDerivAt_inv_log (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => 1/Real.log t) (-mertensKernel x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  convert (Real.hasDerivAt_log hx0).inv hl using 1
  · simp only [one_div]; rfl
  · unfold mertensKernel
    field_simp

lemma mertensKernel_continuousOn (a b : ℝ) (ha : 1 < a) :
    ContinuousOn mertensKernel (Set.Icc a b) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ)<1) (ha.trans_le hx.1))
  have hl : Real.log x ≠ 0 := (Real.log_pos (ha.trans_le hx.1)).ne'
  apply ContinuousAt.continuousWithinAt
  unfold mertensKernel
  fun_prop (disch := simp_all)

lemma mertensKernel_shift_continuousOn (a b σ : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t => mertensKernel t*(Real.log t+σ)) (Set.Icc a b) := by
  apply (mertensKernel_continuousOn a b ha).mul
  apply ContinuousOn.add ?_ continuousOn_const
  intro x hx
  exact (Real.continuousAt_log (ne_of_gt (by linarith [hx.1]))).continuousWithinAt

lemma hasDerivAt_mertens_primitive (x σ : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => Real.log (Real.log t)-σ*(1/Real.log t))
      (mertensKernel x*(Real.log x+σ)) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  convert ((Real.hasDerivAt_log hx0).log hl).sub
    ((hasDerivAt_inv_log x hx).const_mul σ) using 1
  unfold mertensKernel
  field_simp
  ring

lemma integral_mertens_kernel_shift (a b σ : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, mertensKernel t*(Real.log t+σ)) =
      Real.log (Real.log b/Real.log a)+σ*(1/Real.log a-1/Real.log b) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_mertens_primitive x σ
      (ha.trans_le ((Set.uIcc_of_le hab) ▸ hx).1))
    (ContinuousOn.intervalIntegrable_of_Icc hab (mertensKernel_shift_continuousOn a b σ ha))
  rw [h, Real.log_div (Real.log_pos (ha.trans_le hab)).ne' (Real.log_pos ha).ne']
  ring

lemma primeLogMass_floor_log_bound (C : ℝ)
    (H : ∀ N : ℕ, 1 ≤ N → |primeLogMass N-Real.log (N : ℝ)| ≤ C)
    (x : ℝ) (hx : 2 ≤ x) :
    |primeLogMass ⌊x⌋₊-Real.log x| ≤ C+1 := by
  have hx0 : 0 ≤ x := by linarith
  have hn : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hnR : (1 : ℝ) ≤ (⌊x⌋₊ : ℕ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (⌊x⌋₊ : ℕ) := by linarith
  have hf := Nat.floor_le hx0
  have hup : x ≤ 2*(⌊x⌋₊ : ℕ) := by linarith [Nat.lt_floor_add_one x]
  have hlo := Real.log_le_log hn0 hf
  have hhi := Real.log_le_log (by linarith : 0 < x) hup
  rw [Real.log_mul (by norm_num) hn0.ne'] at hhi
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  have habs : |Real.log ((⌊x⌋₊ : ℕ) : ℝ)-Real.log x| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  exact (abs_sub_le _ (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) _).trans
    (_root_.add_le_add (H _ hn) habs)

/-- A general quantitative Abel estimate. The coefficients need not be nonnegative. -/
lemma reciprocal_log_weight_sum_bound (c : ℕ → ℝ) (A B : ℕ) (hA : 2 ≤ A)
    (hAB : A ≤ B) (C : ℝ) (_hC : 0 ≤ C)
    (H : ∀ x ∈ Set.Icc (A : ℝ) B,
      |(∑ k ∈ Icc 0 ⌊x⌋₊, c k)-Real.log x| ≤ C) :
    |(∑ k ∈ Ioc A B, c k/Real.log k)-Real.log (Real.log B/Real.log A)| ≤
      2*C/Real.log A := by
  let M : ℝ → ℝ := fun x => ∑ k ∈ Icc 0 ⌊x⌋₊, c k
  let I : ℝ := ∫ x in (A : ℝ)..B, mertensKernel x*M x
  let R : ℝ := Real.log (Real.log B/Real.log A)
  have hAr : (1 : ℝ) < A := by exact_mod_cast (show 1 < A by omega)
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hBr : (1 : ℝ) < B := hAr.trans_le hABr
  have hlA : 0 < Real.log A := Real.log_pos hAr
  have hlB : 0 < Real.log B := Real.log_pos hBr
  have hK := mertensKernel_continuousOn A B hAr
  have hder (x : ℝ) (hx : x ∈ Set.Icc (A : ℝ) B) :
      deriv (fun t : ℝ => 1/Real.log t) x = -mertensKernel x :=
    (hasDerivAt_inv_log x (hAr.trans_le hx.1)).deriv
  have hfint : IntegrableOn (deriv (fun t : ℝ => 1/Real.log t)) (Set.Icc (A : ℝ) B) := by
    apply hK.neg.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro x hx
    exact (hder x hx).symm
  have hMint : IntervalIntegrable (fun x => mertensKernel x*M x) volume (A : ℝ) B := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hABr).mpr
    exact integrableOn_mul_sum_Icc c (by linarith : (0 : ℝ) ≤ A) hK.integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul' c hAB
    (fun x hx => (hasDerivAt_inv_log x (hAr.trans_le hx.1)).differentiableAt) hfint
  have hneg : (∫ x in Set.Ioc (A : ℝ) B,
      deriv (fun t : ℝ => 1/Real.log t) x * ∑ k ∈ Icc 0 ⌊x⌋₊, c k) = -I := by
    rw [← intervalIntegral.integral_of_le hABr]
    calc
      _ = ∫ x in (A : ℝ)..B, -(mertensKernel x*M x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hABr] at hx
        dsimp only
        rw [hder x hx]
        dsimp [M]
        ring
      _ = _ := intervalIntegral.integral_neg
  rw [hneg, sub_neg_eq_add] at hab
  have hsum : (∑ k ∈ Ioc A B, c k/Real.log k) =
      M B/Real.log B - M A/Real.log A + I := by
    simpa only [M, Nat.floor_natCast, div_eq_mul_inv, one_mul, mul_comm] using hab
  have hMI (σ : ℝ) : IntervalIntegrable
      (fun x => mertensKernel x*(Real.log x+σ)) volume (A : ℝ) B :=
    ContinuousOn.intervalIntegrable_of_Icc hABr (mertensKernel_shift_continuousOn A B σ hAr)
  have hlowI : R-C*(1/Real.log A-1/Real.log B) ≤ I := by
    have hi := intervalIntegral.integral_mono_on hABr (hMI (-C)) hMint (fun x hx =>
      mul_le_mul_of_nonneg_left (by
        have hb := (abs_le.mp (H x hx)).1
        change Real.log x + -C ≤ M x
        linarith only [hb]) (by
          unfold mertensKernel
          have hx0 : 0 ≤ x := le_trans (by linarith : (0 : ℝ) ≤ A) hx.1
          positivity))
    rw [integral_mertens_kernel_shift A B (-C) hAr hABr] at hi
    change _ ≤ I at hi
    dsimp [R]
    linarith only [hi]
  have huppI : I ≤ R+C*(1/Real.log A-1/Real.log B) := by
    have hi := intervalIntegral.integral_mono_on hABr hMint (hMI C) (fun x hx =>
      mul_le_mul_of_nonneg_left (by
        have hb := (abs_le.mp (H x hx)).2
        change M x ≤ Real.log x+C
        linarith only [hb]) (by
          unfold mertensKernel
          have hx0 : 0 ≤ x := le_trans (by linarith : (0 : ℝ) ≤ A) hx.1
          positivity))
    rw [integral_mertens_kernel_shift A B C hAr hABr] at hi
    exact hi
  have hbA := abs_le.mp (H A ⟨le_rfl,hABr⟩)
  have hbB := abs_le.mp (H B ⟨hABr,le_rfl⟩)
  change -C ≤ M A-Real.log A ∧ M A-Real.log A ≤ C at hbA
  change -C ≤ M B-Real.log B ∧ M B-Real.log B ≤ C at hbB
  have hAL : 1-C/Real.log A ≤ M A/Real.log A := by
    apply (le_div_iff₀ hlA).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hlA.ne']
    linarith only [hbA.1]
  have hAU : M A/Real.log A ≤ 1+C/Real.log A := by
    apply (div_le_iff₀ hlA).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hlA.ne']
    linarith only [hbA.2]
  have hBL : 1-C/Real.log B ≤ M B/Real.log B := by
    apply (le_div_iff₀ hlB).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hlB.ne']
    linarith only [hbB.1]
  have hBU : M B/Real.log B ≤ 1+C/Real.log B := by
    apply (div_le_iff₀ hlB).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hlB.ne']
    linarith only [hbB.2]
  change |(∑ k ∈ Ioc A B, c k/Real.log k)-R| ≤ _
  rw [hsum]
  apply abs_le.mpr
  have he : C*(1/Real.log A-1/Real.log B) = C/Real.log A-C/Real.log B := by ring
  rw [he] at hlowI huppI
  rw [mul_div_assoc]
  constructor <;> linarith only [hAL,hAU,hBL,hBU,hlowI,huppI]

end Erdos821
