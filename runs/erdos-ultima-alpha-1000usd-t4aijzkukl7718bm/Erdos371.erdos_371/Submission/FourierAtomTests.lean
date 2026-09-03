import Submission.SpectralWordEnergy
import Submission.DilationSpectralAtoms

/-! Bounded analytic Fourier polynomials concentrating on a single point.
Their squared norms extract atom masses by dominated convergence, including
after dilation. This avoids any unproved density argument for positive tests. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma fourier_sub_argument (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x-y) = fourier n x*conj (fourier n y) := by
  simp only [sub_eq_add_neg,fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul,smul_neg]
  rw [← neg_smul]
  change fourier n x*fourier (-n) y = fourier n x*conj (fourier n y)
  rw [fourier_neg]

lemma fourier_nat_eq_pow (n : ℕ) (x : UnitAddCircle) : fourier (n : ℤ) x = (fourier 1 x)^n := by
  induction n with
  | zero => simp [fourier_zero]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,pow_succ]

noncomputable def fourierAverage (N : ℕ) (x : UnitAddCircle) : ℂ :=
  (∑ k : Fin (N+1), fourier (k : ℤ) x)/(N+1 : ℂ)

lemma continuous_fourierAverage (N : ℕ) : Continuous (fourierAverage N) :=
  (continuous_finset_sum (univ : Finset (Fin (N+1))) (fun k _ => (fourier (k : ℤ)).continuous)).div_const _

lemma fourierAverage_norm_le (N : ℕ) (x : UnitAddCircle) : ‖fourierAverage N x‖ ≤ 1 := by
  have hn : (0 : ℝ) < N+1 := by positivity
  unfold fourierAverage
  rw [norm_div,show (N+1 : ℂ)=((N+1 : ℕ) : ℂ) by simp,Complex.norm_natCast]
  push_cast
  apply (div_le_one hn).mpr
  have hh := norm_sum_le (univ : Finset (Fin (N+1))) (fun k => fourier (k : ℤ) x)
  simpa only [fourier_apply,Circle.norm_coe,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,mul_one] using hh

lemma fourierAverage_zero (N : ℕ) : fourierAverage N 0 = 1 := by
  have hn : (N+1 : ℂ) ≠ 0 := by exact_mod_cast (show N+1≠0 by omega)
  simp [fourierAverage,fourier_eval_zero,hn]

lemma fourier_one_ne_one {x : UnitAddCircle} (hx : x ≠ 0) : fourier 1 x ≠ 1 := by
  intro he
  apply hx
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.coe_injective
  simpa only [fourier_one,AddCircle.toCircle_zero,OneMemClass.coe_one] using he

lemma fourierAverage_tendsto_zero {x : UnitAddCircle} (hx : x ≠ 0) :
    Tendsto (fun N => fourierAverage N x) atTop (𝓝 0) := by
  let z : ℂ := fourier 1 x
  have hz : z ≠ 1 := fourier_one_ne_one hx
  have hzn : ‖z‖ = 1 := Circle.norm_coe _
  have hz1 : 0 < ‖z-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hb (N : ℕ) : ‖fourierAverage N x‖ ≤ (2/‖z-1‖)/(N+1 : ℝ) := by
    have he : fourierAverage N x = ((z^(N+1)-1)/(z-1))/(N+1 : ℂ) := by
      unfold fourierAverage
      simp_rw [fourier_nat_eq_pow]
      rw [Fin.sum_univ_eq_sum_range,geom_sum_eq hz]
    rw [he,norm_div,norm_div,show (N+1 : ℂ)=((N+1 : ℕ) : ℂ) by simp,Complex.norm_natCast]
    push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ hz1.le
    exact (norm_sub_le _ _).trans (by norm_num [norm_pow,hzn])
  have ht : Tendsto (fun N : ℕ => (2/‖z-1‖)/(N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun N : ℕ => show (N : ℝ) ≤ N+1 by linarith) tendsto_natCast_atTop_atTop)
  exact squeeze_zero_norm hb ht

lemma fourierAverage_sq_tendsto (x : UnitAddCircle) :
    Tendsto (fun N => ‖fourierAverage N x‖^2) atTop (𝓝 (if x=0 then (1 : ℝ) else 0)) := by
  by_cases hx : x=0
  · subst x
    simp only [fourierAverage_zero,norm_one,one_pow,if_pos rfl]
    exact tendsto_const_nhds
  · simpa only [norm_zero,zero_pow (by norm_num : 2≠0),if_neg hx] using
      (fourierAverage_tendsto_zero hx).norm.pow 2

/-- A single bounded family extracts either a point mass or the mass of a
fiber of any fixed continuous map. -/
lemma fourierAverage_integral_atom (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (T : C(UnitAddCircle,UnitAddCircle)) (a : UnitAddCircle) :
    Tendsto (fun N => ∫ x, ‖fourierAverage N (T x-a)‖^2 ∂μ) atTop
      (𝓝 (μ.real {x | T x=a})) := by
  have hmeas : MeasurableSet {x | T x=a} := (measurableSet_singleton a).preimage T.continuous.measurable
  have hm (N : ℕ) : AEStronglyMeasurable (fun x => ‖fourierAverage N (T x-a)‖^2) μ :=
    (((continuous_fourierAverage N).comp (T.continuous.sub continuous_const)).norm.pow 2).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ x ∂μ, ‖‖fourierAverage N (T x-a)‖^2‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hh := fourierAverage_norm_le N (T x-a)
    nlinarith [norm_nonneg (fourierAverage N (T x-a))]
  have ht (x : UnitAddCircle) : Tendsto (fun N => ‖fourierAverage N (T x-a)‖^2) atTop
      (𝓝 (({x | T x=a} : Set UnitAddCircle).indicator (fun _ => (1 : ℝ)) x)) := by
    simpa only [Set.indicator_apply,Set.mem_setOf_eq,sub_eq_zero] using fourierAverage_sq_tendsto (T x-a)
  have hd := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm (integrable_const 1) hb
    (Eventually.of_forall ht)
  have hi : (∫ x, ({x | T x=a} : Set UnitAddCircle).indicator (fun _ => (1 : ℝ)) x ∂μ) =
      μ.real {x | T x=a} := integral_indicator_one hmeas
  rw [hi] at hd
  exact hd

lemma fourierAverage_eq_spectralPolynomial (N : ℕ) (a x : UnitAddCircle) :
    fourierAverage N (x-a) = spectralPolynomial
      (fun k : Fin (N+1) => conj (fourier (k : ℤ) a)/(N+1 : ℂ)) (fun k => k) x := by
  simp only [fourierAverage,spectralPolynomial,fourier_sub_argument,sum_div]
  apply sum_congr rfl
  intro k hk
  ring

/-- Analytic polynomial energy inequalities imply the exact atom-fiber
inequality, which is enough for the earlier disjoint-fiber argument. -/
theorem atom_fiber_bound_of_polynomial_energy (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (p : ℕ)
    (hpoly : ∀ K : ℕ, ∀ a : Fin K → ℂ,
      (∫ x, ‖spectralPolynomial a (fun k => k) x‖^2 ∂μ) ≤
        p*∫ x, ‖spectralPolynomial a (fun k => k) (p • x)‖^2 ∂μ)
    (a : UnitAddCircle) : μ.real {a} ≤ p*μ.real {x | p • x=a} := by
  let T : C(UnitAddCircle,UnitAddCircle) := ⟨fun x => p • x,continuous_id.nsmul p⟩
  have hleft := fourierAverage_integral_atom μ (ContinuousMap.id _) a
  have hright := (fourierAverage_integral_atom μ T a).const_mul (p : ℝ)
  have hh := le_of_tendsto_of_tendsto' hleft hright (fun N => ?_)
  · simpa only [ContinuousMap.id_apply,Set.setOf_eq_eq_singleton,T,ContinuousMap.coe_mk] using hh
  · simpa only [fourierAverage_eq_spectralPolynomial,T,ContinuousMap.coe_mk,ContinuousMap.id_apply] using
      hpoly (N+1) (fun k : Fin (N+1) => conj (fourier (k : ℤ) a)/(N+1 : ℂ))

#print axioms atom_fiber_bound_of_polynomial_energy
end Erdos371.DilationSpectrum
