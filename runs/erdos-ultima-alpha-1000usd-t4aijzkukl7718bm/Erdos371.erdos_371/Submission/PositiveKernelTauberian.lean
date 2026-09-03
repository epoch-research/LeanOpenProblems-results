import Submission.BandlimitedApproximateIdentity

/-! A bounded, slowly decreasing function tends to zero if it has decaying
means for positive probability kernels with arbitrarily small first moment.
This is the final real-variable squeeze in the bounded Tauberian argument. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform
open scoped Topology
set_option autoImplicit false

noncomputable def kernelMean (K f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, K u*f (x+u)

lemma kernelMean_integrable (K f : ℝ → ℝ) (hK : Integrable K)
    (hf : AEStronglyMeasurable f) (M : ℝ) (hM : ∀ t, |f t| ≤ M) (x : ℝ) :
    Integrable (fun u => K u*f (x+u)) := by
  apply hK.mul_bdd (hf.comp_measurePreserving (measurePreserving_add_left volume x))
  exact Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hM (x+u))

lemma kernelMean_translation (K f : ℝ → ℝ) (x : ℝ) :
    kernelMean K f x = ∫ t, f t*K (t-x) := by
  unfold kernelMean
  have hi := integral_add_left_eq_self (μ := volume) (fun t => f t*K (t-x)) x
  simp only [add_sub_cancel_left] at hi
  rw [← hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => mul_comm _ _)

lemma kernelMean_neg (K f : ℝ → ℝ) (x : ℝ) :
    kernelMean K (fun t => -f t) x = -kernelMean K f x := by
  simp only [kernelMean,mul_neg,integral_neg]

/-- A one-sided local bound becomes a global smoothed bound, with explicit
first-moment error. No support restriction on the kernel is needed. -/
lemma one_sided_kernel_bound
    (K f : ℝ → ℝ) (hK : Integrable K) (hKpos : ∀ u, 0 ≤ K u)
    (hKmass : (∫ u, K u) = 1) (hMom : Integrable (fun u => |u| *K u))
    (hf : AEStronglyMeasurable f) (M : ℝ) (hMpos : 0 ≤ M) (hM : ∀ t, |f t| ≤ M)
    (a c δ ε : ℝ) (ha : |a| ≤ M) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hlocal : ∀ u, |u| ≤ δ → a-f (c+u) ≤ ε) :
    a-kernelMean K f c ≤ ε+(2*M/δ)*(∫ u, |u| *K u) := by
  have hpoint (u : ℝ) : a-f (c+u) ≤ ε+(2*M/δ)*|u| := by
    by_cases hu : |u| ≤ δ
    · exact (hlocal u hu).trans (le_add_of_nonneg_right (by positivity))
    · have hbase : a-f (c+u) ≤ 2*M := by
        have h₁ := (abs_le.mp ha).2
        have h₂ := (abs_le.mp (hM (c+u))).1
        linarith
      have hh : 2*M ≤ (2*M/δ)*|u| := by
        have hu' : δ ≤ |u| := (lt_of_not_ge hu).le
        have he : (2*M/δ)*δ = 2*M := div_mul_cancel₀ _ hδ.ne'
        calc
          2*M = (2*M/δ)*δ := he.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hu' (by positivity)
      linarith
  have hi := integral_mono
    ((hK.mul_const a).sub (kernelMean_integrable K f hK hf M hM c))
    ((hK.const_mul ε).add (hMom.const_mul (2*M/δ))) (fun u => ?_)
  · simp only [Pi.sub_apply,Pi.add_apply] at hi
    rw [integral_sub,integral_add,integral_mul_const,integral_const_mul,integral_const_mul,hKmass] at hi
    · simpa only [one_mul,mul_one,kernelMean] using hi
    · exact hK.const_mul ε
    · exact hMom.const_mul _
    · exact hK.mul_const a
    · exact kernelMean_integrable K f hK hf M hM c
  · calc
      K u*a-K u*f (c+u) = K u*(a-f (c+u)) := by ring
      _ ≤ K u*(ε+(2*M/δ)*|u|) := mul_le_mul_of_nonneg_left (hpoint u) (hKpos u)
      _ = ε*K u+(2*M/δ)*(|u| *K u) := by ring

/-- Slow decrease is one-sided; continuity is not assumed. -/
def SlowlyDecreasing (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧ ∃ T : ℝ,
    ∀ x y : ℝ, T ≤ x → x ≤ y → y ≤ x+d → f x-f y ≤ ε

theorem tendsto_zero_of_small_moment_kernel_means
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f)
    (M : ℝ) (hMpos : 0 < M) (hM : ∀ t, |f t| ≤ M)
    (hslow : SlowlyDecreasing f)
    (hkernels : ∀ η : ℝ, 0 < η → ∃ K : ℝ → ℝ,
      Integrable K ∧ (∀ u, 0 ≤ K u) ∧ (∫ u, K u) = 1 ∧
      Integrable (fun u => |u| *K u) ∧ (∫ u, |u| *K u) ≤ η ∧
      Tendsto (kernelMean K f) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d,hd,T,hslow⟩ := hslow (ε/4) (by positivity)
  let δ := d/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let η := ε*δ/(8*M)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K,hK,hKpos,hKmass,hMom,hmom,hlim⟩ := hkernels η hη
  have herror : (2*M/δ)*(∫ u, |u| *K u) ≤ ε/4 := by
    calc
      _ ≤ (2*M/δ)*η := mul_le_mul_of_nonneg_left hmom (by positivity)
      _ = _ := by dsimp [η]; field_simp; ring
  have hfuture := hlim.comp (tendsto_atTop_add_const_right atTop δ tendsto_id)
  have hpast := hlim.comp (tendsto_atTop_add_const_right atTop (-δ) tendsto_id)
  filter_upwards [(Metric.tendsto_nhds.mp hfuture) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hpast) (ε/4) (by positivity),eventually_ge_atTop (T+d)] with x hfuture hpast hx
  simp only [Real.dist_eq,sub_zero,Function.comp_apply,id_eq] at hfuture hpast ⊢
  have hupper := one_sided_kernel_bound K f hK hKpos hKmass hMom hf M hMpos.le hM
    (f x) (x+δ) δ (ε/4) (hM x) hδ (by positivity) (fun u hu => ?_)
  · have hlower := one_sided_kernel_bound K (fun t => -f t) hK hKpos hKmass hMom hf.neg M hMpos.le
      (fun t => by simpa only [abs_neg] using hM t)
      (-f x) (x-δ) δ (ε/4) (by simpa only [abs_neg] using hM x) hδ (by positivity) (fun u hu => ?_)
    · rw [kernelMean_neg] at hlower
      have hfut := (abs_lt.mp hfuture).2
      have hpast' := (abs_lt.mp hpast).1
      rw [← sub_eq_add_neg] at hpast'
      rw [abs_lt]
      constructor <;> linarith
    · have hu' := abs_le.mp hu
      have h := hslow ((x-δ)+u) x (by dsimp [δ] at *; linarith)
        (by dsimp [δ] at *; linarith) (by dsimp [δ] at *; linarith)
      linarith
  · have hu' := abs_le.mp hu
    exact hslow x ((x+δ)+u) (by dsimp [δ] at *; linarith)
      (by dsimp [δ] at *; linarith) (by dsimp [δ] at *; linarith)

#print axioms tendsto_zero_of_small_moment_kernel_means
end Erdos371.FourierBoundary
