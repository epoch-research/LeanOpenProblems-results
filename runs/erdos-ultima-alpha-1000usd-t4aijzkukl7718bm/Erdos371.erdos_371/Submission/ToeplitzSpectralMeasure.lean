import Submission.ToeplitzFourierDensity

/-! Herglotz representation for a positive Hermitian Toeplitz sequence,
constructed from finite nonnegative Fourier densities and compactness. -/
namespace Erdos371.DilationSpectrum
open Finset MeasureTheory Filter Complex TopologicalSpace
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma toeplitz_zero_nonneg (c : ℤ → ℂ) (hc : ToeplitzPositive c) : 0 ≤ (c 0).re := by
  simpa using hc 1 (fun _ => 1)

noncomputable def toeplitzRawMeasure (c : ℤ → ℂ) (N : ℕ) : Measure UnitAddCircle :=
  AddCircle.haarAddCircle.withDensity (fun x => ENNReal.ofReal (toeplitzDensity c (N+1) x))

lemma toeplitzRawMeasure_univ (c : ℤ → ℂ) (hc : ∀ k, c (-k)=conj (c k))
    (hpos : ToeplitzPositive c) (N : ℕ) : toeplitzRawMeasure c N Set.univ = ENNReal.ofReal (c 0).re := by
  rw [toeplitzRawMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((continuous_toeplitzDensity c (N+1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Eventually.of_forall (toeplitzDensity_nonneg c hpos (N+1)))]
  rw [integral_toeplitzDensity c hc (N+1) (by omega)]

noncomputable def toeplitzMeasure (c : ℤ → ℂ) (hc : ∀ k, c (-k)=conj (c k))
    (hpos : ToeplitzPositive c) (N : ℕ) : FiniteMeasure UnitAddCircle :=
  ⟨toeplitzRawMeasure c N,⟨by rw [toeplitzRawMeasure_univ c hc hpos]; finiteness⟩⟩

lemma integral_toeplitzMeasure_fourier (c : ℤ → ℂ) (hc : ∀ k, c (-k)=conj (c k))
    (hpos : ToeplitzPositive c) (N : ℕ) (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂(toeplitzMeasure c hc hpos N : Measure UnitAddCircle)) =
      ((N+1-k.natAbs : ℕ) : ℂ)/(N+1 : ℂ)*c k := by
  change (∫ x, fourier k x ∂toeplitzRawMeasure c N) = _
  have hm : Measurable (fun x => ENNReal.ofReal (toeplitzDensity c (N+1) x)) :=
    (ENNReal.continuous_ofReal.comp (continuous_toeplitzDensity c (N+1))).measurable
  rw [toeplitzRawMeasure,integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall (fun _ => by finiteness))]
  have he (x : UnitAddCircle) : (ENNReal.ofReal (toeplitzDensity c (N+1) x)).toReal • fourier k x =
      (toeplitzDensity c (N+1) x : ℂ)*fourier k x := by
    rw [ENNReal.toReal_ofReal (toeplitzDensity_nonneg c hpos (N+1) x)]
    rfl
  simp_rw [he]
  simpa only [Nat.cast_add,Nat.cast_one] using integral_toeplitzDensity_mul_fourier c hc (N+1) k

lemma toeplitzMeasure_mass_bound (c : ℤ → ℂ) (hc : ∀ k, c (-k)=conj (c k))
    (hpos : ToeplitzPositive c) (N : ℕ) :
    (toeplitzMeasure c hc hpos N).mass ≤ ⟨(c 0).re,toeplitz_zero_nonneg c hpos⟩ := by
  apply ENNReal.coe_le_coe.mp
  rw [FiniteMeasure.ennreal_mass]
  change toeplitzRawMeasure c N Set.univ ≤ _
  rw [toeplitzRawMeasure_univ c hc hpos]
  change ENNReal.ofReal ((⟨(c 0).re,toeplitz_zero_nonneg c hpos⟩ : NNReal) : ℝ) ≤ _
  exact le_of_eq ENNReal.ofReal_coe_nnreal

lemma truncated_ratio_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ => ((N+1-k : ℕ) : ℂ)/(N+1 : ℂ)) atTop (𝓝 1) := by
  have ht : Tendsto (fun N : ℕ => (k : ℝ)/(N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono (fun N : ℕ => show (N : ℝ) ≤ N+1 by linarith) tendsto_natCast_atTop_atTop)
  have hh := Complex.continuous_ofReal.tendsto (1-0) |>.comp (tendsto_const_nhds.sub ht)
  simp only [sub_zero,ofReal_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop k] with N hN
  dsimp only [Function.comp_apply]
  rw [Nat.cast_sub (by omega : k≤N+1)]
  push_cast
  have hNZ : (N+1 : ℂ) ≠ 0 := by exact_mod_cast (show N+1≠0 by omega)
  field_simp

lemma toeplitzMeasure_fourier_tendsto (c : ℤ → ℂ) (hc : ∀ k, c (-k)=conj (c k))
    (hpos : ToeplitzPositive c) (k : ℤ) :
    Tendsto (fun N => ∫ x : UnitAddCircle, fourier k x
      ∂(toeplitzMeasure c hc hpos N : Measure UnitAddCircle)) atTop (𝓝 (c k)) := by
  simp_rw [integral_toeplitzMeasure_fourier]
  simpa only [one_mul] using (truncated_ratio_tendsto k.natAbs).mul_const (c k)

lemma continuous_finiteMeasure_integral_complex {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (F : C(X,ℂ)) :
    Continuous (fun μ : FiniteMeasure X => ∫ x, F x ∂(μ : Measure X)) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp tendsto_id
    (ContinuousMap.equivBoundedOfCompact X ℂ F)

/-- Every positive Hermitian Toeplitz sequence is represented by the Fourier
moments of a finite positive measure on the unit circle. -/
theorem exists_toeplitz_spectral_measure (c : ℤ → ℂ)
    (hc : ∀ k, c (-k)=conj (c k)) (hpos : ToeplitzPositive c) :
    ∃ μ : FiniteMeasure UnitAddCircle, ∀ k : ℤ,
      (∫ x, fourier k x ∂(μ : Measure UnitAddCircle)) = c k := by
  let C : NNReal := ⟨(c 0).re,toeplitz_zero_nonneg c hpos⟩
  have hcompact := isCompact_setOf_finiteMeasure_le_of_compactSpace UnitAddCircle C
  obtain ⟨μ,hμ,hcluster⟩ := hcompact.exists_mapClusterPt
    (f := (atTop : Filter ℕ)) (u := toeplitzMeasure c hc hpos)
    (le_principal_iff.mpr (Filter.mem_map.mpr (Eventually.of_forall (fun N => toeplitzMeasure_mass_bound c hc hpos N))))
  refine ⟨μ,?_⟩
  intro k
  have hcl := hcluster.continuousAt_comp (continuous_finiteMeasure_integral_complex (fourier k)).continuousAt
  have ht : Tendsto ((fun ν : FiniteMeasure UnitAddCircle => ∫ x, fourier k x ∂(ν : Measure UnitAddCircle)) ∘
      toeplitzMeasure c hc hpos) atTop (𝓝 (c k)) := toeplitzMeasure_fourier_tendsto c hc hpos k
  exact eq_of_nhds_neBot (hcl.clusterPt.mono ht).neBot

#print axioms exists_toeplitz_spectral_measure
end Erdos371.DilationSpectrum
