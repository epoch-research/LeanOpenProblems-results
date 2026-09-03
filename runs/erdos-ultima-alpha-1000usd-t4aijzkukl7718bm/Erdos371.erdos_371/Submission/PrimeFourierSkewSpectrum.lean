import Submission.AtomlessPrimeFourierAverage
import Submission.NaturalCyclicPrimeSkew

/-! Prime-averaged imaginary Fourier moments vanish for finite circle
measures having no atoms of infinite order. Rational atoms use fixed-modulus
PNT-AP; the atomless complement uses the proved prime L2 theorem. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma primeFourierAverage_norm_le (N : ℕ) (x : UnitAddCircle) : ‖primeFourierAverage N x‖ ≤ 1 := by
  have hb := norm_sum_le (initialPrimes N) (fun p => fourier (p : ℤ) x)
  simp only [fourier_apply,Circle.norm_coe,sum_const,nsmul_eq_mul,mul_one] at hb
  rw [primeFourierAverage,norm_div,Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)).trans (div_self_le_one _)

lemma integral_im_bound_by_energy {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F : C(X,ℂ)) (δ : ℝ) (hδ : 0 < δ) :
    |∫ x, (F x).im ∂μ| ≤ δ*μ.real Set.univ+(∫ x, ‖F x‖^2 ∂μ)/δ := by
  have hfi : Integrable (fun x => |(F x).im|) μ :=
    (Complex.continuous_im.comp F.continuous).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (fun x => δ+‖F x‖^2/δ) μ :=
    (continuous_const.add (F.continuous.norm.pow 2 |>.div_const δ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb (x : X) : |(F x).im| ≤ δ+‖F x‖^2/δ := by
    apply (Complex.abs_im_le_norm _).trans
    rw [show δ+‖F x‖^2/δ = (δ^2+‖F x‖^2)/δ by field_simp]
    apply (le_div_iff₀ hδ).mpr
    nlinarith [sq_nonneg (‖F x‖-δ)]
  have hi := integral_mono hfi hgi hb
  have hnorm := norm_integral_le_integral_norm (fun x => (F x).im) (μ := μ)
  simp only [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  apply hi.trans_eq
  rw [integral_add (integrable_const δ)
    (((F.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).div_const δ),
    integral_const,integral_div,smul_eq_mul,mul_comm (μ.real Set.univ) δ]

lemma integral_im_zero_of_energy_zero {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F : ℕ → C(X,ℂ))
    (hE : Tendsto (fun N => ∫ x, ‖F N x‖^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ x, (F N x).im ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M := μ.real Set.univ
  let δ := ε/(2*(M+1))
  have hM : 0 ≤ M := measureReal_nonneg
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδM : δ*M < ε/2 := by
    have he : δ*(2*(M+1))=ε := by dsimp [δ]; field_simp
    nlinarith
  have ht := hE.div_const δ
  simp only [zero_div] at ht
  filter_upwards [ht.eventually_lt_const (show (0 : ℝ)<ε/2 by positivity)] with N hN
  rw [Real.dist_eq,sub_zero]
  exact (integral_im_bound_by_energy μ (F N) δ hδ).trans_lt (by linarith)

lemma atomless_primeFourier_im_integral_zero (μ : Measure UnitAddCircle)
    [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto (fun N => ∫ x, (primeFourierAverage N x).im ∂μ) atTop (𝓝 0) :=
  integral_im_zero_of_energy_zero μ (fun N => ⟨primeFourierAverage N,continuous_primeFourierAverage N⟩)
    (atomless_primeFourierAverage_L2_zero μ)

lemma primeFourier_im_torsion_zero (x : UnitAddCircle) (hx : IsOfFinAddOrder x) :
    Tendsto (fun N => (primeFourierAverage N x).im) atTop (𝓝 0) := by
  obtain ⟨q,hq,hqx⟩ := hx.exists_nsmul_eq_zero
  letI : NeZero q := ⟨hq.ne'⟩
  let ψ : {F : ℤ →+ UnitAddCircle // F q=0} :=
    ⟨zmultiplesHom UnitAddCircle x,by simpa only [zmultiplesHom_apply,natCast_zsmul] using hqx⟩
  let φ : ZMod q →+ UnitAddCircle := ZMod.lift q ψ
  have hφ (n : ℕ) : φ (n : ZMod q) = n • x := by
    have hh := ZMod.lift_coe q ψ (n : ℤ)
    simpa only [Int.cast_natCast,φ,ψ,zmultiplesHom_apply,natCast_zsmul] using hh
  let g : ZMod q → ℝ := fun r => (fourier 1 (φ r)).im
  have hg (r : ZMod q) : g (-r) = -g r := by
    dsimp only [g]
    rw [map_neg]
    have he := fourier_sub_argument 1 (0 : UnitAddCircle) (φ r)
    simp only [zero_sub,fourier_eval_zero,one_mul] at he
    rw [he,conj_im]
  have hn (n : ℕ) : g (n : ZMod q) = (fourier (n : ℤ) x).im := by
    dsimp only [g]
    rw [hφ]
    have he := fourier_nsmul_nat n 1 x
    simpa only [Nat.cast_one,mul_one] using congrArg Complex.im he
  have ht := prime_periodic_odd_natural_limit g hg
  have him (N : ℕ) : (∑ p ∈ initialPrimes N, fourier (p : ℤ) x).im =
      ∑ p ∈ initialPrimes N, (fourier (p : ℤ) x).im :=
    map_sum Complex.imAddGroupHom _ _
  simpa only [primeFourierAverage,Complex.div_natCast_im,him,hn] using ht

def torsionCircle : Set UnitAddCircle := {x | IsOfFinAddOrder x}

lemma torsionCircle_countable : torsionCircle.Countable := by
  apply (Set.countable_range (fun q : ℚ => ((q : ℝ) : UnitAddCircle))).mono
  intro x hx
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨q,hq⟩ := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div.mp hx
  refine ⟨q,?_⟩
  simpa only [div_one] using congrArg (fun r : ℝ => (r : UnitAddCircle)) hq

lemma torsionCircle_measurable : MeasurableSet torsionCircle := torsionCircle_countable.measurableSet

lemma noAtoms_restrict_torsion_compl (μ : Measure UnitAddCircle)
    (hno : ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → μ {x}=0) : NoAtoms (μ.restrict torsionCircleᶜ) := by
  constructor
  intro x
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : IsOfFinAddOrder x
  · have he : ({x} : Set UnitAddCircle) ∩ torsionCircleᶜ = ∅ := by
      ext y
      simp only [Set.mem_inter_iff,Set.mem_singleton_iff,Set.mem_compl_iff,Set.mem_empty_iff_false,torsionCircle,
        Set.mem_setOf_eq]
      aesop
    rw [he,measure_empty]
  · exact measure_mono_null Set.inter_subset_left (hno x hx)

lemma torsion_primeFourier_im_integral_zero (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] :
    Tendsto (fun N => ∫ x, (primeFourierAverage N x).im ∂μ.restrict torsionCircle) atTop (𝓝 0) := by
  have hm (N : ℕ) : AEStronglyMeasurable (fun x => (primeFourierAverage N x).im) (μ.restrict torsionCircle) :=
    (Complex.continuous_im.comp (continuous_primeFourierAverage N)).aestronglyMeasurable
  have hb (N : ℕ) : ∀ᵐ x ∂μ.restrict torsionCircle, ‖(primeFourierAverage N x).im‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (primeFourierAverage_norm_le N x)
  have ht : ∀ᵐ x ∂μ.restrict torsionCircle, Tendsto (fun N => (primeFourierAverage N x).im) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem torsionCircle_measurable] with x hx
    exact primeFourier_im_torsion_zero x hx
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm (integrable_const 1) hb ht

/-- Ordinary prime-averaged imaginary Fourier moments vanish whenever all
atoms are rational. The atomless part may be singular; no absolute
continuity or pointwise Fourier-decay assumption is made. -/
theorem primeFourier_im_integral_zero_of_no_infinite_order_atoms
    (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (hno : ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → μ {x}=0) :
    Tendsto (fun N => ∫ x, (primeFourierAverage N x).im ∂μ) atTop (𝓝 0) := by
  letI := noAtoms_restrict_torsion_compl μ hno
  have ht := (torsion_primeFourier_im_integral_zero μ).add
    (atomless_primeFourier_im_integral_zero (μ.restrict torsionCircleᶜ))
  simp only [add_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  exact integral_add_compl torsionCircle_measurable
    ((Complex.continuous_im.comp (continuous_primeFourierAverage N)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

#print axioms primeFourier_im_integral_zero_of_no_infinite_order_atoms
end Erdos371.DilationSpectrum
