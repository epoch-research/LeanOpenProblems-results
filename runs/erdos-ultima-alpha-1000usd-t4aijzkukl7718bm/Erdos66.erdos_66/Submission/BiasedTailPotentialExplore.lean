import Submission.VariableBernoulliBoundsExplore

/-! An exponential majorant of a deviation event with a slightly biased mean. -/
namespace Erdos66BiasedTailPotential
open Erdos66FiniteBernoulli
open scoped Classical
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000

noncomputable def potential (δ T x : ℝ) : ℝ :=
  Real.exp ((δ/16)*(x-T-δ*T)) + Real.exp (-(δ/16)*(x-T+δ*T))

lemma potential_nonneg (δ T x : ℝ) : 0 ≤ potential δ T x := by unfold potential; positivity

lemma potential_continuous (δ T : ℝ) : Continuous (potential δ T) := by
  unfold potential
  fun_prop

lemma one_le_potential (δ T x : ℝ) (hδ : 0 ≤ δ) (hbad : δ*T ≤ |x-T|) :
    1 ≤ potential δ T x := by
  rcases le_abs.mp hbad with h|h
  · have hh : 0 ≤ (δ/16)*(x-T-δ*T) := mul_nonneg (by positivity) (by linarith)
    have he := Real.one_le_exp_iff.mpr hh
    unfold potential
    linarith [Real.exp_pos (-(δ/16)*(x-T+δ*T))]
  · have hh : 0 ≤ -(δ/16)*(x-T+δ*T) := mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (by positivity)) (by linarith)
    have he := Real.one_le_exp_iff.mpr hh
    unfold potential
    linarith [Real.exp_pos ((δ/16)*(x-T-δ*T))]

lemma expect_potential_bound (p : ι → ℝ) (F : (ι → Bool) → ℝ)
    (m T δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : m ≤ 2*T) (hbias : |m-T| ≤ δ*T/2)
    (hmgf : ∀ t : ℝ, |t| ≤ 1/2 →
      expect p (fun ω ↦ Real.exp (t*(F ω-m))) ≤ Real.exp (2*t^2*m)) :
    expect p (fun ω ↦ potential δ T (F ω)) ≤ 2*Real.exp (-δ^2*T/64) := by
  let t := δ/16
  have ht : 0<t := by dsimp [t]; positivity
  have htbound : |t| ≤ 1/2 := by rw [abs_of_pos ht]; dsimp [t]; linarith
  have hntbound : |-t| ≤ 1/2 := by simpa only [abs_neg] using htbound
  have hplus := mul_le_mul_of_nonneg_left (abs_le.mp hbias).2 ht.le
  have hminus := mul_le_mul_of_nonneg_left (abs_le.mp hbias).1 ht.le
  have hvar := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*t^2 by positivity)
  have he₁ : t*(m-T-δ*T)+2*t^2*m ≤ -δ^2*T/64 := by
    calc
      _ ≤ -t*δ*T/2+4*t^2*T := by nlinarith
      _ = _ := by dsimp [t]; ring
  have he₂ : -t*(m-T+δ*T)+2*t^2*m ≤ -δ^2*T/64 := by
    calc
      _ ≤ -t*δ*T/2+4*t^2*T := by nlinarith
      _ = _ := by dsimp [t]; ring
  have h₁ : expect p (fun ω ↦ Real.exp (t*(F ω-T-δ*T))) ≤ Real.exp (-δ^2*T/64) := by
    have he (ω : ι → Bool) : Real.exp (t*(F ω-T-δ*T)) =
        Real.exp (t*(m-T-δ*T))*Real.exp (t*(F ω-m)) := by
      rw [←Real.exp_add]; congr 1; ring
    simp_rw [he]
    rw [expect_const_mul]
    have hh := mul_le_mul_of_nonneg_left (hmgf t htbound) (Real.exp_pos (t*(m-T-δ*T))).le
    rw [←Real.exp_add] at hh
    exact hh.trans (Real.exp_le_exp.mpr he₁)
  have h₂ : expect p (fun ω ↦ Real.exp (-t*(F ω-T+δ*T))) ≤ Real.exp (-δ^2*T/64) := by
    have he (ω : ι → Bool) : Real.exp (-t*(F ω-T+δ*T)) =
        Real.exp (-t*(m-T+δ*T))*Real.exp (-t*(F ω-m)) := by
      rw [←Real.exp_add]; congr 1; ring
    simp_rw [he]
    rw [expect_const_mul]
    have hh := mul_le_mul_of_nonneg_left (hmgf (-t) hntbound) (Real.exp_pos (-t*(m-T+δ*T))).le
    rw [neg_sq,←Real.exp_add] at hh
    exact hh.trans (Real.exp_le_exp.mpr he₂)
  unfold potential
  rw [expect_add]
  change expect p (fun ω ↦ Real.exp (t*(F ω-T-δ*T))) +
    expect p (fun ω ↦ Real.exp (-t*(F ω-T+δ*T))) ≤ _
  linarith

end Erdos66BiasedTailPotential
