import Submission.SingularWeightedWiener

/-! Ordinary prime Fourier averages converge to zero in L2 of every
atomless finite measure. Prime-pair sieving and Wiener's lemma suffice; no
pointwise irrational-frequency prime theorem is invoked. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteSieve AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

noncomputable def primeFourierAverage (N : ℕ) (x : UnitAddCircle) : ℂ :=
  (∑ p ∈ initialPrimes N, fourier (p : ℤ) x)/((initialPrimes N).card : ℂ)

lemma continuous_primeFourierAverage (N : ℕ) : Continuous (primeFourierAverage N) :=
  (continuous_finset_sum (initialPrimes N) (fun p _ => (fourier (p : ℤ)).continuous)).div_const _

lemma fourier_sum_energy_bound (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] (S : Finset ℕ) :
    (∫ x, ‖∑ p ∈ S, fourier (p : ℤ) x‖^2 ∂μ) ≤ ∑ p ∈ S, ∑ q ∈ S, ‖measureFourier μ ((p : ℤ)-q)‖ := by
  have he := integral_sum_mul_conj μ (fun _ : S => (1 : ℂ)) (fun p : S => fourier ((p : ℕ) : ℤ))
    (fun p => (fourier ((p : ℕ) : ℤ)).continuous)
  simp only [one_mul,map_one,mul_one,Finset.sum_coe_sort S] at he
  have hpair (p q : ℕ) : (∫ x : UnitAddCircle, fourier (p : ℤ) x*conj (fourier (q : ℤ) x) ∂μ) =
      measureFourier μ ((p : ℤ)-q) := by
    simp only [← fourier_neg,← fourier_add,sub_eq_add_neg,measureFourier]
  simp only [hpair,Complex.mul_conj,Complex.normSq_eq_norm_sq,integral_complex_ofReal] at he
  have hs (x : UnitAddCircle) : (∑ p : S, fourier ((p : ℕ) : ℤ) x) = ∑ p ∈ S, fourier (p : ℤ) x :=
    Finset.sum_coe_sort S (fun p : ℕ => fourier (p : ℤ) x)
  have hi (p : ℕ) : (∑ q : S, measureFourier μ ((p : ℤ)-(q : ℕ))) =
      ∑ q ∈ S, measureFourier μ ((p : ℤ)-q) :=
    Finset.sum_coe_sort S (fun q : ℕ => measureFourier μ ((p : ℤ)-q))
  simp_rw [hs,hi] at he
  rw [Finset.sum_coe_sort S (fun p : ℕ => ∑ q ∈ S, measureFourier μ ((p : ℤ)-q))] at he
  have hn := congrArg norm he
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun x => sq_nonneg _))] at hn
  rw [hn]
  exact (norm_sum_le _ _).trans (sum_le_sum fun p _ => norm_sum_le _ _)

lemma primeFourier_energy_finite_bound (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] (N : ℕ) :
    (∫ x, ‖primeFourierAverage N x‖^2 ∂μ) ≤
      ((initialPrimes N).card*‖measureFourier μ 0‖+
        (2*primeDifferenceSieveConstant*(N+1 : ℝ)/(Real.log (N+2 : ℝ))^2)*
          ∑ k ∈ range N, slopeSieveFactor (2*(k+1))*‖measureFourier μ (k+1 : ℕ)‖)/
            ((initialPrimes N).card : ℝ)^2 := by
  have hh := (fourier_sum_energy_bound μ (initialPrimes N)).trans
    (initialPrimes_even_difference_bound N (fun k => ‖measureFourier μ k‖)
      (fun k => by dsimp only; rw [measureFourier_neg,norm_conj]) (fun k => norm_nonneg _))
  simp only [primeFourierAverage,norm_div,Complex.norm_natCast,div_pow,integral_div]
  exact div_le_div_of_nonneg_right hh (sq_nonneg _)

lemma initialPrimes_card_tendsto : Tendsto (fun N => (initialPrimes N).card) atTop atTop := by
  simp only [initialPrimes_eq_primesBelow,Nat.primesBelow_card_eq_primeCounting']
  exact Nat.tendsto_primeCounting

lemma initialPrimes_card_positive (N : ℕ) (hN : 2 ≤ N) : 0 < (initialPrimes N).card := by
  apply card_pos.mpr
  exact ⟨2,mem_filter.mpr ⟨mem_Icc.mpr ⟨by norm_num,hN⟩,Nat.prime_two⟩⟩

lemma primeFourier_energy_eventual_bound (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] :
    ∀ᶠ N : ℕ in atTop,
      (∫ x, ‖primeFourierAverage N x‖^2 ∂μ) ≤
        ‖measureFourier μ 0‖/(initialPrimes N).card+16*primeDifferenceSieveConstant*singularFourierMean μ N := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    prime_number_theorem_initial.eventually_const_lt (by norm_num : (1/2 : ℝ)<1)] with N hN hP
  let P : ℝ := (initialPrimes N).card
  let L : ℝ := Real.log (N+2 : ℝ)
  let C : ℝ := primeDifferenceSieveConstant
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hP0 : 0 < P := by
    change (0 : ℝ) < ((initialPrimes N).card : ℝ)
    exact_mod_cast initialPrimes_card_positive N hN
  have hL : 0 < L := Real.log_pos (by linarith)
  have hC : 0 ≤ C := by dsimp [C,primeDifferenceSieveConstant]; positivity
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hlogL : Real.log (N : ℝ) ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hNp : (N : ℝ) ≤ 2*P*Real.log N := by
    change 1/2<P*Real.log N/N at hP
    have hh := (lt_div_iff₀ (show (0 : ℝ)<N by positivity)).mp hP
    linarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) N) hNp 2
  have hlog2 := pow_le_pow_left₀ hlog hlogL 2
  have hsqL := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ 4*P^2 by positivity)
  have hsize : (N+1 : ℝ)*N ≤ 8*L^2*P^2 := by nlinarith
  have hratio : 2*C*(N+1 : ℝ)*N/(L^2*P^2) ≤ 16*C := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hL) (sq_pos_of_pos hP0))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsize (show (0 : ℝ) ≤ 2*C by positivity)]
  have hsum : (∑ k ∈ range N, slopeSieveFactor (2*(k+1))*‖measureFourier μ (k+1 : ℕ)‖) =
      N*singularFourierMean μ N := by unfold singularFourierMean; field_simp
  have hh := primeFourier_energy_finite_bound μ N
  rw [hsum] at hh
  have he : ((initialPrimes N).card*‖measureFourier μ 0‖+
      (2*primeDifferenceSieveConstant*(N+1 : ℝ)/(Real.log (N+2 : ℝ))^2)*(N*singularFourierMean μ N))/
        ((initialPrimes N).card : ℝ)^2 =
        ‖measureFourier μ 0‖/P+(2*C*(N+1 : ℝ)*N/(L^2*P^2))*singularFourierMean μ N := by
    dsimp [P,L,C]
    field_simp
    <;> ring
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hratio (singularFourierMean_nonneg μ N)))

/-- Prime averages are L2-null against any atomless finite circle measure.
Only a fixed finite measure is asserted, not uniformity over changing ones. -/
theorem atomless_primeFourierAverage_L2_zero (μ : Measure UnitAddCircle)
    [IsFiniteMeasure μ] [NoAtoms μ] :
    Tendsto (fun N => ∫ x, ‖primeFourierAverage N x‖^2 ∂μ) atTop (𝓝 0) := by
  have hP : Tendsto (fun N => ((initialPrimes N).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp initialPrimes_card_tendsto
  have hd : Tendsto (fun N => ‖measureFourier μ 0‖/(initialPrimes N).card) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hP
  have hw := (atomless_singularFourierMean_zero μ).const_mul (16*primeDifferenceSieveConstant)
  have hh := hd.add hw
  simp only [mul_zero,add_zero] at hh
  exact squeeze_zero' (Eventually.of_forall (fun N => integral_nonneg (fun x => sq_nonneg _)))
    (primeFourier_energy_eventual_bound μ) hh

#print axioms atomless_primeFourierAverage_L2_zero
end Erdos371.DilationSpectrum
