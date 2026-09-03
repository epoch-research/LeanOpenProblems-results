import FormalConjecturesUtil

/-! A finite-measure obstruction to irrational spectral atoms. This is an
abstract result, not yet an assertion about a largest-prime-factor limit.
Domination by all dilation pushforwards excludes atoms of infinite order. -/
namespace Erdos371.DilationSpectrum
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable {G : Type*} [AddCommGroup G]

lemma dilation_fibers_pairwise_disjoint (x : G) (hx : ¬IsOfFinAddOrder x) :
    Pairwise (fun n m : ℕ => Disjoint {y : G | n • y = x} {y : G | m • y = x}) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro y hy hy'
  have hyinf : ¬IsOfFinAddOrder y := by
    intro hfin
    exact hx (hy ▸ hfin.nsmul)
  exact hnm ((injective_nsmul_iff_not_isOfFinAddOrder.mpr hyinf) (hy.trans hy'.symm))

/-- The total fiber masses are summable; reciprocal lower bounds at a single
infinite-order atom would force the harmonic series to be summable. -/
theorem singleton_zero_of_dilation_fiber_bound [MeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasure μ] (x : G) (hx : ¬IsOfFinAddOrder x)
    (hmeas : ∀ n : ℕ, MeasurableSet {y : G | n • y = x})
    (hdom : ∀ n : ℕ, 0 < n → μ.real {x} ≤ n*μ.real {y : G | n • y = x}) :
    μ {x} = 0 := by
  have hs : Summable (fun n : ℕ => μ.real {y : G | n • y = x}) :=
    summable_measure_toReal hmeas (dilation_fibers_pairwise_disjoint x hx)
  have hc := measureReal_nonneg (μ := μ) (s := {x})
  have hsmall : Summable (fun n : ℕ => μ.real {x}/n) := by
    apply hs.of_nonneg_of_le (fun n => div_nonneg hc (Nat.cast_nonneg n))
    intro n
    by_cases hn : n = 0
    · simp only [hn,Nat.cast_zero,div_zero]
      exact measureReal_nonneg
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      apply (div_le_iff₀ hn').mpr
      simpa only [mul_comm] using hdom n (Nat.pos_of_ne_zero hn)
  have hz : μ.real {x} = 0 := by
    by_contra h
    have ht := hsmall.div_const (μ.real {x})
    apply Real.not_summable_one_div_natCast
    convert ht using 1
    funext n
    field_simp
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top μ {x})

/-- Measure domination is the form expected from positivity after restricting
a harmonic average to the residue class zero modulo n. -/
theorem singleton_zero_of_dilation_domination [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T1Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasure μ]
    (hdom : ∀ n : ℕ, 0 < n → μ ≤ (n : ℝ≥0∞) • μ.map (fun y => n • y))
    (x : G) (hx : ¬IsOfFinAddOrder x) : μ {x} = 0 := by
  have hm (n : ℕ) : Measurable (fun y : G => n • y) := (continuous_id.nsmul n).measurable
  apply singleton_zero_of_dilation_fiber_bound μ x hx
  · intro n
    exact (measurableSet_singleton x).preimage (hm n)
  · intro n hn
    have hd := hdom n hn {x}
    rw [Measure.smul_apply,Measure.map_apply (hm n) (measurableSet_singleton x)] at hd
    have hfin : (n : ℝ≥0∞)*μ {y | n • y = x} ≠ ⊤ := ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)
    have hr := ENNReal.toReal_mono hfin hd
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,Measure.real] using hr

/-- On the unit circle, infinite additive order is precisely irrationality. -/
theorem irrational_singleton_zero_of_dilation_domination
    (μ : Measure (AddCircle (1 : ℝ))) [IsFiniteMeasure μ]
    (hdom : ∀ n : ℕ, 0 < n → μ ≤ (n : ℝ≥0∞) • μ.map (fun y => n • y))
    (a : ℝ) (ha : Irrational a) : μ {(a : AddCircle (1 : ℝ))} = 0 := by
  apply singleton_zero_of_dilation_domination μ hdom
  simpa only [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div,div_one] using ha

#print axioms singleton_zero_of_dilation_domination
#print axioms irrational_singleton_zero_of_dilation_domination
end Erdos371.DilationSpectrum
