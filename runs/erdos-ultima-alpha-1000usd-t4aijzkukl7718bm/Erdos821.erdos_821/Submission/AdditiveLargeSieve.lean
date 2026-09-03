import FormalConjecturesUtil

/-!
# Finite analytic large-sieve tools

These are unconditional analytic estimates, not a settlement of Erdős 821.
In particular they do not assert the needed lower bounds for primes in
progressions to growing smooth moduli.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace Erdos821.AnalyticSieve

lemma point_sampling_bound (f f' : ℝ → ℝ) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt f (f' x) x) (a δ : ℝ) (hδ : 0 ≤ δ) :
    δ * f a ≤ (∫ x in a..a + δ, f x) + δ * ∫ x in a..a + δ, |f' x| := by
  have hab : a ≤ a + δ := by linarith
  have hp (x : ℝ) (hx : x ∈ Icc a (a + δ)) :
      f a ≤ f x + ∫ t in a..a + δ, |f' t| := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hd t) (hf'.intervalIntegrable a x)
    have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := f') (μ := volume) hx.1
    rw [heq, Real.norm_eq_abs] at hnorm
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall (fun t => abs_nonneg (f' t)))
      (hf'.abs.intervalIntegrable a (a + δ))
    have hh : |f x - f a| ≤ ∫ t in a..a + δ, |f' t| := by
      apply hnorm.trans
      simpa only [Real.norm_eq_abs] using hmono
    have hh' := neg_le_abs (f x - f a)
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (continuous_const.intervalIntegrable a (a + δ))
    ((hf.add continuous_const).intervalIntegrable a (a + δ)) hp
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hf.intervalIntegrable a (a + δ))
      (continuous_const.intervalIntegrable a (a + δ)), intervalIntegral.integral_const] at hi
  simpa only [add_sub_cancel_left, smul_eq_mul] using hi

lemma sum_interval_integrals_le {ι : Type*} (I : Finset ι) (x : ι → ℝ)
    (δ U : ℝ) (hδ : 0 ≤ δ) (hU : 0 ≤ U)
    (hx : ∀ i ∈ I, 0 ≤ x i ∧ x i + δ ≤ U)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → δ ≤ |x i - x j|)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) :
    (∑ i ∈ I, ∫ t in x i..x i + δ, f t) ≤ ∫ t in (0 : ℝ)..U, f t := by
  classical
  have hdisj : Set.Pairwise (↑I) (fun i j => Disjoint (Ioc (x i) (x i + δ)) (Ioc (x j) (x j + δ))) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hs := hsep i hi j hj hij
    rcases le_total (x i) (x j) with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hs
      linarith [hti.2, htj.1]
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hs
      linarith [htj.2, hti.1]
  have hsub : (⋃ i ∈ I, Ioc (x i) (x i + δ)) ⊆ Ioc 0 U := by
    intro t ht
    obtain ⟨i, hi, ht⟩ := Set.mem_iUnion₂.mp ht
    exact ⟨lt_of_le_of_lt (hx i hi).1 ht.1, ht.2.trans (hx i hi).2⟩
  simp_rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hδ)]
  rw [← integral_biUnion_finset I (fun i _ => measurableSet_Ioc) hdisj
    (fun i _ => hf.integrableOn_Ioc), intervalIntegral.integral_of_le hU]
  exact setIntegral_mono_set hf.integrableOn_Ioc
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hsub)

lemma finite_sampling_bound {ι : Type*} (I : Finset ι) (x : ι → ℝ)
    (δ U : ℝ) (hδ : 0 ≤ δ) (hU : 0 ≤ U)
    (hx : ∀ i ∈ I, 0 ≤ x i ∧ x i + δ ≤ U)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → δ ≤ |x i - x j|)
    (f f' : ℝ → ℝ) (hf : Continuous f) (hf' : Continuous f')
    (hf0 : ∀ t, 0 ≤ f t) (hd : ∀ t, HasDerivAt f (f' t) t) :
    δ * (∑ i ∈ I, f (x i)) ≤
      (∫ t in (0 : ℝ)..U, f t) + δ * ∫ t in (0 : ℝ)..U, |f' t| := by
  calc
    _ ≤ ∑ i ∈ I, ((∫ t in x i..x i + δ, f t) + δ * ∫ t in x i..x i + δ, |f' t|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => point_sampling_bound f f' hf hf' hd (x i) δ hδ)
    _ = (∑ i ∈ I, ∫ t in x i..x i + δ, f t) +
        δ * (∑ i ∈ I, ∫ t in x i..x i + δ, |f' t|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add
      (sum_interval_integrals_le I x δ U hδ hU hx hsep f hf hf0)
      (mul_le_mul_of_nonneg_left
        (sum_interval_integrals_le I x δ U hδ hU hx hsep _ hf'.abs (fun _ => abs_nonneg _)) hδ)

noncomputable def wave (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I) * x)

lemma continuous_wave (n : ℤ) : Continuous (wave n) := by unfold wave; fun_prop

lemma hasDerivAt_wave (n : ℤ) (x : ℝ) :
    HasDerivAt (wave n) ((n : ℂ) * (2 * Real.pi * Complex.I) * wave n x) x := by
  convert (((hasDerivAt_id (x : ℂ)).const_mul
    ((n : ℂ) * (2 * Real.pi * Complex.I))).comp_ofReal).cexp using 1;
    simp only [wave, id_eq, one_mul, mul_comm]

lemma wave_add (m n : ℤ) (x : ℝ) : wave (m + n) x = wave m x * wave n x := by
  unfold wave
  rw [Int.cast_add, add_mul, add_mul, Complex.exp_add]

lemma conj_wave (n : ℤ) (x : ℝ) : (starRingEnd ℂ) (wave n x) = wave (-n) x := by
  unfold wave
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_intCast, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Int.cast_neg]
  ring

lemma integral_wave (n : ℤ) :
    (∫ x in (0 : ℝ)..2, wave n x) = if n = 0 then 2 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [wave]
  · have hc : (n : ℂ) * (2 * Real.pi * Complex.I) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hn)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    rw [if_neg hn]
    unfold wave
    rw [integral_exp_mul_complex hc]
    have hexp : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I) * 2) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (2 * n) using 1
      push_cast
      ring_nf
    simp only [Complex.ofReal_ofNat, Complex.ofReal_zero, hexp, mul_zero,
      Complex.exp_zero, sub_self, zero_div]

noncomputable def trigSum (A : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ A, a n * wave n x

lemma continuous_trigSum (A : Finset ℤ) (a : ℤ → ℂ) : Continuous (trigSum A a) := by
  unfold trigSum
  exact continuous_finset_sum _ (fun n _ => continuous_const.mul (continuous_wave n))

lemma integral_trigSum_norm_sq (A : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..2, ‖trigSum A a x‖ ^ 2) = 2 * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  classical
  have hexpand (x : ℝ) : ((‖trigSum A a x‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ A, ∑ n ∈ A, (a m * (starRingEnd ℂ) (a n)) * wave (m - n) x := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [trigSum, map_sum, map_mul, Finset.sum_mul_sum, conj_wave, sub_eq_add_neg, wave_add]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finset_sum (fun m _ =>
    (continuous_finset_sum _ (fun n _ => continuous_const.mul (continuous_wave (m - n)))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finset_sum (fun n _ =>
      (continuous_const.mul (continuous_wave _)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_wave, sub_eq_zero]
  simp only [mul_ite, mul_zero]
  have hsum (m : ℤ) (hm : m ∈ A) :
      (∑ n ∈ A, if m = n then (a m * (starRingEnd ℂ) (a n)) * 2 else 0) =
        (a m * (starRingEnd ℂ) (a m)) * 2 := by
    simp [Finset.sum_ite_eq, hm]
  rw [Finset.sum_congr rfl hsum]
  simp only [Complex.mul_conj', Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_pow, mul_comm]
  rw [Finset.mul_sum]

noncomputable def derivCoeffs (a : ℤ → ℂ) (n : ℤ) : ℂ :=
  a n * ((n : ℂ) * (2 * Real.pi * Complex.I))

lemma hasDerivAt_trigSum (A : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) :
    HasDerivAt (trigSum A a) (trigSum A (derivCoeffs a) x) x := by
  simpa only [trigSum, derivCoeffs, mul_assoc] using
    (HasDerivAt.fun_sum (u := A) (fun n _ => (hasDerivAt_wave n x).const_mul (a n)))

lemma norm_derivCoeffs_le (a : ℤ → ℂ) (n : ℤ) (N : ℝ) (hn : |(n : ℝ)| ≤ N) :
    ‖derivCoeffs a n‖ ≤ (2 * Real.pi * N) * ‖a n‖ := by
  unfold derivCoeffs
  simp only [norm_mul, Complex.norm_intCast, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  have h := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ ‖a n‖ * (2 * Real.pi))
  nlinarith only [h]

lemma integral_trigSum_deriv_norm_sq_le (A : Finset ℤ) (a : ℤ → ℂ)
    (N : ℝ) (hA : ∀ n ∈ A, |(n : ℝ)| ≤ N) :
    (∫ x in (0 : ℝ)..2, ‖trigSum A (derivCoeffs a) x‖ ^ 2) ≤
      (2 * Real.pi * N) ^ 2 * (2 * ∑ n ∈ A, ‖a n‖ ^ 2) := by
  rw [integral_trigSum_norm_sq]
  calc
    _ ≤ 2 * ∑ n ∈ A, ((2 * Real.pi * N) * ‖a n‖) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun n hn =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_derivCoeffs_le a n N (hA n hn)) _)
    _ = _ := by simp only [mul_pow, ← Finset.mul_sum]; ring

lemma abs_norm_sq_deriv_le (z w : ℂ) (R : ℝ) (hR : 0 < R) :
    |2 * inner ℝ z w| ≤ R * ‖z‖ ^ 2 + ‖w‖ ^ 2 / R := by
  have hinner := abs_real_inner_le_norm z w
  have hsq := sq_nonneg (R * ‖z‖ - ‖w‖)
  have hbound : 2 * ‖z‖ * ‖w‖ ≤ R * ‖z‖ ^ 2 + ‖w‖ ^ 2 / R := by
    calc
      _ ≤ (R ^ 2 * ‖z‖ ^ 2 + ‖w‖ ^ 2) / R :=
        (le_div_iff₀ hR).mpr (by nlinarith only [hsq])
      _ = _ := by field_simp
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith only [hinner, hbound]

/-- A non-sharp additive large sieve, proved by disjoint-interval sampling
and the energy identity for a trigonometric polynomial. -/
theorem additive_large_sieve {ι : Type*} (I : Finset ι) (x : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : ∀ i ∈ I, 0 ≤ x i ∧ x i ≤ 1)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → δ ≤ |x i - x j|)
    (A : Finset ℤ) (a : ℤ → ℂ) (N : ℝ) (hN : 0 ≤ N)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ N) :
    (∑ i ∈ I, ‖trigSum A a (x i)‖ ^ 2) ≤
      (2 / δ + 4 * (2 * Real.pi * N + 1)) * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  let S := trigSum A a
  let D := trigSum A (derivCoeffs a)
  let E := ∑ n ∈ A, ‖a n‖ ^ 2
  let c := 2 * Real.pi * N
  let R := c + 1
  let f' : ℝ → ℝ := fun t => 2 * inner ℝ (S t) (D t)
  have hS : Continuous S := continuous_trigSum A a
  have hD : Continuous D := continuous_trigSum A (derivCoeffs a)
  have hf' : Continuous f' := continuous_const.mul (hS.inner hD)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hR : 0 < R := by dsimp [R]; linarith
  have hRE : (∫ t in (0 : ℝ)..2, ‖S t‖ ^ 2) = 2 * E := integral_trigSum_norm_sq A a
  have hDE : (∫ t in (0 : ℝ)..2, ‖D t‖ ^ 2) ≤ c ^ 2 * (2 * E) :=
    integral_trigSum_deriv_norm_sq_le A a N hA
  have hderiv : (∫ t in (0 : ℝ)..2, |f' t|) ≤ 4 * R * E := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..2, R * ‖S t‖ ^ 2 + ‖D t‖ ^ 2 / R :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hf'.abs.intervalIntegrable _ _)
          (((continuous_const.mul (hS.norm.pow 2)).add ((hD.norm.pow 2).div_const R)).intervalIntegrable _ _)
            (fun t _ => abs_norm_sq_deriv_le (S t) (D t) R hR)
      _ = R * (2 * E) + (∫ t in (0 : ℝ)..2, ‖D t‖ ^ 2) / R := by
        rw [intervalIntegral.integral_add
          ((continuous_const.mul (hS.norm.pow 2)).intervalIntegrable _ _)
          (((hD.norm.pow 2).div_const R).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_div, hRE]
      _ ≤ R * (2 * E) + (c ^ 2 * (2 * E)) / R :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hDE hR.le)
      _ ≤ R * (2 * E) + R * (2 * E) := by
        apply add_le_add le_rfl
        apply (div_le_iff₀ hR).mpr
        have hcsq : c ^ 2 ≤ R ^ 2 := by dsimp [R]; nlinarith
        have hh := mul_le_mul_of_nonneg_right hcsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
        nlinarith only [hh]
      _ = _ := by ring
  have hsamp := finite_sampling_bound I x δ 2 hδ.le (by norm_num)
    (fun i hi => ⟨(hx i hi).1, by linarith [(hx i hi).2]⟩) hsep
    (fun t => ‖S t‖ ^ 2) f' (hS.norm.pow 2) hf' (fun _ => sq_nonneg _)
    (fun t => (hasDerivAt_trigSum A a t).norm_sq)
  rw [hRE] at hsamp
  have hb := hsamp.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hderiv hδ.le))
  change (∑ i ∈ I, ‖S (x i)‖ ^ 2) ≤ (2 / δ + 4 * R) * E
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    δ * (∑ i ∈ I, ‖S (x i)‖ ^ 2) ≤ 2 * E + δ * (4 * R * E) := hb
    _ = δ * ((2 / δ + 4 * R) * E) := by field_simp


lemma rational_separation (Q : ℕ) (r s : ℚ) (hr : r.den ≤ Q) (hs : s.den ≤ Q)
    (hne : r ≠ s) : 1 / (Q : ℝ) ^ 2 ≤ |(r : ℝ) - (s : ℝ)| := by
  have hrd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsd : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  let b : ℤ := r.num * s.den - s.num * r.den
  have hid : ((r : ℝ) - (s : ℝ)) * ((r.den : ℝ) * s.den) = (b : ℝ) := by
    dsimp [b]
    rw [Rat.cast_def r, Rat.cast_def s]
    push_cast
    field_simp
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, Int.cast_zero] at hid
    have heq : (r : ℝ) = s := by
      have hh := (mul_eq_zero.mp hid).resolve_right (mul_pos hrd hsd).ne'
      exact sub_eq_zero.mp hh
    exact hne (Rat.cast_injective heq)
  have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
  rw [← hid, abs_mul, abs_of_pos (mul_pos hrd hsd)] at hb1
  have hden : (r.den : ℝ) * s.den ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast (show r.den * s.den ≤ Q ^ 2 by
      simpa only [pow_two] using Nat.mul_le_mul hr hs)
  calc
    1 / (Q : ℝ) ^ 2 ≤ 1 / ((r.den : ℝ) * s.den) :=
      one_div_le_one_div_of_le (mul_pos hrd hsd) hden
    _ ≤ _ := (div_le_iff₀ (mul_pos hrd hsd)).mpr hb1

/-- The additive large sieve over any finite set of reduced rational
points in `[0,1]` with denominators at most `Q`. -/
theorem rational_large_sieve (I : Finset ℚ) (Q : ℕ) (hQ : 0 < Q)
    (hI : ∀ r ∈ I, 0 ≤ r ∧ r ≤ 1 ∧ r.den ≤ Q)
    (A : Finset ℤ) (a : ℤ → ℂ) (N : ℝ) (hN : 0 ≤ N)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ N) :
    (∑ r ∈ I, ‖trigSum A a (r : ℝ)‖ ^ 2) ≤
      (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * N + 1)) * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hδ1 : 1 / (Q : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hQR)).mpr
    nlinarith
  have h := additive_large_sieve I (fun r : ℚ => (r : ℝ)) (1 / (Q : ℝ) ^ 2) hδ hδ1
    (fun r hr => ⟨by dsimp; exact_mod_cast (hI r hr).1, by dsimp; exact_mod_cast (hI r hr).2.1⟩)
    (fun r hr s hs hrs => rational_separation Q r s (hI r hr).2.2 (hI s hs).2.2 hrs)
    A a N hN hA
  simpa only [one_div, div_inv_eq_mul] using h

#print axioms integral_trigSum_norm_sq
#print axioms additive_large_sieve
#print axioms rational_separation
#print axioms rational_large_sieve

end Erdos821.AnalyticSieve
