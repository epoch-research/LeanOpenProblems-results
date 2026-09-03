import Submission.SmallPrimeAmbientMean

/-!
# Quantitative decay for the small-prime two-cofactor mean

The finite bounds give an exponentially small relative error in m, not
just an unspecified o(1). Consequently every fixed polynomial in m, or
power of the logarithm of the full product range, can be absorbed.
These are still congruence means, not prime-successor lower bounds.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Kloosterman
open Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma squarefree_rectangle_kernel_rate (A : ℝ) (hA : 0 ≤ A) (m : ℕ) :
    A*(rectangleModulusScale m : ℝ)^(1/72 : ℝ)*
      rectangleMeanKernel (rectangleModulusScale m) (rectangleIntervalScale m)
        (rectangleIntervalScale m) ≤
      (22000*A*((m : ℝ)+1)^2/(2 : ℝ)^m)*(rectangleIntervalScale m : ℝ)^2 := by
  rw [rectangleModulusScale_small_rpow]
  calc
    _ ≤ A*(2 : ℝ)^m*(22000*((m : ℝ)+1)^2*(2 : ℝ)^(126*m)) :=
      mul_le_mul_of_nonneg_left (rectangleMeanKernel_scale_bound m) (by positivity)
    _ = (22000*A*((m : ℝ)+1)^2)*(2 : ℝ)^(127*m) := by
      rw [show A*(2 : ℝ)^m*(22000*((m : ℝ)+1)^2*(2 : ℝ)^(126*m)) =
        (22000*A*((m : ℝ)+1)^2)*((2 : ℝ)^m*(2 : ℝ)^(126*m)) by ring,
        ← pow_add]
      congr 2
      omega
    _ = _ := by
      have he : (rectangleIntervalScale m : ℝ)^2 = (2 : ℝ)^m*(2 : ℝ)^(127*m) := by
        simp only [rectangleIntervalScale, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul,
          ← pow_add]
        congr 1
        omega
      rw [he]
      field_simp

lemma rectangle_prime_nonunit_rate (m : ℕ) :
    (harmonic (rectangleModulusScale m) : ℝ)/(2 : ℝ)^m ≤
      73*((m : ℝ)+1)^2/(2 : ℝ)^m := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := harmonic_two_pow_le (72*m)
  unfold rectangleModulusScale
  push_cast at hh
  nlinarith [sq_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) m]

end Erdos821.Kloosterman
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman Erdos821.SuccessorAvoidance

/-- Uniform finite exponential decay, independent of the size or density
of the nonnegative prime-supported input weight. -/
theorem exists_doubleCofactor_small_prime_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ 2^m ≤ n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (rectangleIntervalScale m) (rectangleIntervalScale m) X-
        squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
      (C*((m : ℝ)+1)^2/(2 : ℝ)^m)*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  obtain ⟨A,hA,HA⟩ := doubleCofactor_squarefree_prime_mean (1/72) (by norm_num)
  refine ⟨22000*A+73, by positivity, ?_⟩
  intro m f hf hs P hP X M N u
  have h1 := mul_le_mul_of_nonneg_right (squarefree_rectangle_kernel_rate A hA.le m)
    (restrictedMass_nonneg f hf X)
  have hrec := primeReciprocalMass_le f hf (2^m) X (by positivity)
    (fun n hn => (hs n hn).2)
  have h2 : (rectangleIntervalScale m : ℝ)*rectangleIntervalScale m*
      (harmonic (rectangleModulusScale m) : ℝ)*primeReciprocalMass f X ≤
      (73*((m : ℝ)+1)^2/(2 : ℝ)^m)*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
    have hrec' := mul_le_mul_of_nonneg_left hrec
      (show 0 ≤ (rectangleIntervalScale m : ℝ)*rectangleIntervalScale m*
        (harmonic (rectangleModulusScale m) : ℝ) by
        positivity [harmonic_natCast_nonneg (rectangleModulusScale m)])
    have hcoef := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (rectangle_prime_nonunit_rate m)
        (show 0 ≤ (rectangleIntervalScale m : ℝ)^2 by positivity))
      (restrictedMass_nonneg f hf X)
    push_cast at hrec'
    apply hrec'.trans
    convert hcoef using 1; ring
  have h := (HA f hf (fun n hn => (hs n hn).1) P _ _ _ X M N u hP).trans
    (_root_.add_le_add h1 h2)
  convert h using 1; ring

/-- The relative error absorbs every fixed polynomial in the scale
parameter. All quantifiers on weights and moduli remain uniform. -/
theorem eventually_doubleCofactor_small_prime_poly_rate (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ 2^m ≤ n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      ((m : ℝ)+1)^d*(∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (rectangleIntervalScale m) (rectangleIntervalScale m) X-
        squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
        η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X := by
  obtain ⟨C,hC,HC⟩ := exists_doubleCofactor_small_prime_rate
  have ht := (tendsto_shifted_poly_div_two_pow (d+2)).const_mul C
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const hη] with m hm
  intro f hf hs P hP X M N u
  have h := mul_le_mul_of_nonneg_left (HC m f hf hs P hP X M N u)
    (show 0 ≤ ((m : ℝ)+1)^d by positivity)
  have hc : ((m : ℝ)+1)^d*(C*((m : ℝ)+1)^2/(2 : ℝ)^m) ≤ η := by
    have hh : C*(((m : ℝ)+1)^(d+2)/(2 : ℝ)^m) ≤ η := hm.le
    rw [pow_add] at hh
    convert hh using 1; ring
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (show 0 ≤ (rectangleIntervalScale m : ℝ)^2 by positivity))
    (restrictedMass_nonneg f hf X)
  apply h.trans
  convert hb using 1; ring

lemma smallPrimeAmbientScale_log_le (m : ℕ) :
    1+Real.log (smallPrimeAmbientScale m : ℝ) ≤ 131*((m : ℝ)+1) := by
  rw [smallPrimeAmbientScale_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have ht : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have h := mul_le_mul_of_nonneg_left ht (show 0 ≤ ((130*m : ℕ) : ℝ) by positivity)
  push_cast at h ⊢
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Every fixed power of the logarithm of the displayed scale A is absorbed.
A bounds the products when p <= smallPrimeInputTop m, as packaged below.
The theorem makes no claim about prime successors. -/
theorem eventually_small_prime_successor_log_rate (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → 2^m ≤ p →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      (1+Real.log (smallPrimeAmbientScale m : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range (rectangleIntervalScale m),
          ∑ j ∈ range (rectangleIntervalScale m),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*(rectangleIntervalScale m : ℝ)^2 := by
  filter_upwards [eventually_doubleCofactor_small_prime_poly_rate d (η/(131 : ℝ)^d)
    (by positivity)] with m hm
  intro p hp hlo P hP
  have hs : ∀ n, singletonPrimeWeight p hp n ≠ 0 → n.Prime ∧ 2^m ≤ n := by
    intro n hn
    rw [singletonPrimeWeight_support p hp n hn]
    exact ⟨hp,hlo⟩
  have h := hm (singletonPrimeWeight p hp) (singletonPrimeWeight_nonneg p hp)
    hs P hP p 1 1 (fun _ => -1)
  simp only [singletonPrimeWeight_cofactor, squarefreeCofactorMain,
    singletonPrimeWeight_mass, mul_one, ← sq, doubleCofactorRow_neg_one_natural] at h
  have hlog : 0 ≤ 1+Real.log (smallPrimeAmbientScale m : ℝ) := by
    have hA : (1 : ℝ) ≤ smallPrimeAmbientScale m := by
      rw [smallPrimeAmbientScale_eq]
      exact_mod_cast (Nat.one_le_pow _ _ (by decide : 1 ≤ 2))
    positivity [Real.log_nonneg hA]
  have hpow := pow_le_pow_left₀ hlog (smallPrimeAmbientScale_log_le m) d
  rw [mul_pow] at hpow
  have hsum : 0 ≤ (∑ q ∈ P, |(∑ i ∈ range (rectangleIntervalScale m),
      ∑ j ∈ range (rectangleIntervalScale m),
        if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
      (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) :=
    sum_nonneg (fun _ _ => abs_nonneg _)
  apply (mul_le_mul_of_nonneg_right hpow hsum).trans
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (131 : ℝ)^d by positivity)
  convert hh using 1 <;> field_simp

/-- A nonvacuous, full-ambient beyond-half congruence mean with arbitrary
fixed logarithmic savings. This is not a prime-successor supply. -/
theorem eventually_exists_prime_successor_log_rate (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^m < p ∧ p ≤ smallPrimeInputTop m ∧
      rectangleModulusScale m^65 = smallPrimeAmbientScale m^36 ∧
      smallPrimeAmbientScale m+1 < rectangleModulusScale m^2 ∧
      (∀ a ∈ Icc 1 (rectangleIntervalScale m), ∀ b ∈ Icc 1 (rectangleIntervalScale m),
        a*b*p ≤ smallPrimeAmbientScale m) ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      (1+Real.log (smallPrimeAmbientScale m : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range (rectangleIntervalScale m),
          ∑ j ∈ range (rectangleIntervalScale m),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*(rectangleIntervalScale m : ℝ)^2 := by
  filter_upwards [eventually_small_prime_successor_log_rate d η hη, eventually_ge_atTop 1]
    with m Hm hm
  obtain ⟨p,hp,hlo,hhi⟩ := exists_prime_in_smallPrimeInputRange m hm
  refine ⟨p,hp,hlo,hhi,smallPrimeAmbient_power_relation m,smallPrimeAmbient_above_half m hm,?_,
    Hm p hp hlo.le⟩
  intro a ha b hb
  exact smallPrime_rectangle_product_bound m p a b hhi (mem_Icc.mp ha).2 (mem_Icc.mp hb).2

end Erdos821.AnalyticSieve
