import Submission.ParametricRectangleKernel

/-!
# Parametric small-prime means with logarithmic savings

These are estimates for two free cofactor intervals. No prime-successor
lower bound, or new totient multiplicity exponent, is asserted.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman Erdos821.SuccessorAvoidance
set_option maxHeartbeats 3000000

/-- Uniform finite exponential decay, independent of the size or density
of the nonnegative prime-supported input weight. -/
theorem exists_parametric_small_prime_rate (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ 2^m ≤ n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ parametricModulus k m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (parametricInterval k m) (parametricInterval k m) X-
        squarefreeCofactorMain f q (parametricInterval k m) (parametricInterval k m) X|) ≤
      (C*((m : ℝ)+1)^2/(2 : ℝ)^m)*(parametricInterval k m : ℝ)^2*restrictedMass f X := by
  obtain ⟨A,hA,HA⟩ := doubleCofactor_squarefree_prime_mean (1/(8*(k : ℝ)+4)) (by positivity)
  refine ⟨300*A*((k : ℝ)+1)^2+8*((k : ℝ)+1), by positivity, ?_⟩
  intro m f hf hs P hP X M N u
  have h1 := mul_le_mul_of_nonneg_right (parametric_rectangle_kernel_rate k m hk A hA.le)
    (restrictedMass_nonneg f hf X)
  have hrec := primeReciprocalMass_le f hf (2^m) X (by positivity)
    (fun n hn => (hs n hn).2)
  have h2 : (parametricInterval k m : ℝ)*parametricInterval k m*
      (harmonic (parametricModulus k m) : ℝ)*primeReciprocalMass f X ≤
      (8*((k : ℝ)+1)*((m : ℝ)+1)^2/(2 : ℝ)^m)*(parametricInterval k m : ℝ)^2*restrictedMass f X := by
    have hrec' := mul_le_mul_of_nonneg_left hrec
      (show 0 ≤ (parametricInterval k m : ℝ)*parametricInterval k m*
        (harmonic (parametricModulus k m) : ℝ) by
        positivity [harmonic_natCast_nonneg (parametricModulus k m)])
    have hcoef := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (parametric_nonunit_rate k m)
        (show 0 ≤ (parametricInterval k m : ℝ)^2 by positivity))
      (restrictedMass_nonneg f hf X)
    push_cast at hrec'
    apply hrec'.trans
    convert hcoef using 1; ring
  have h := (HA f hf (fun n hn => (hs n hn).1) P _ _ _ X M N u hP).trans
    (_root_.add_le_add h1 h2)
  convert h using 1; ring

/-- The relative error absorbs every fixed polynomial in the scale
parameter. All quantifiers on weights and moduli remain uniform. -/
theorem eventually_parametric_small_prime_poly_rate (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ 2^m ≤ n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ parametricModulus k m) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      ((m : ℝ)+1)^d*(∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (parametricInterval k m) (parametricInterval k m) X-
        squarefreeCofactorMain f q (parametricInterval k m) (parametricInterval k m) X|) ≤
        η*(parametricInterval k m : ℝ)^2*restrictedMass f X := by
  obtain ⟨C,hC,HC⟩ := exists_parametric_small_prime_rate k hk
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
    (mul_le_mul_of_nonneg_right hc (show 0 ≤ (parametricInterval k m : ℝ)^2 by positivity))
    (restrictedMass_nonneg f hf X)
  apply h.trans
  convert hb using 1; ring

/-- Every fixed power of the logarithm of the displayed scale A is absorbed.
A bounds the products when p <= smallPrimeInputTop m, as packaged below.
The theorem makes no claim about prime successors. -/
theorem eventually_parametric_successor_log_rate (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → 2^m ≤ p →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ parametricModulus k m) →
      (1+Real.log (parametricAmbient k m : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range (parametricInterval k m),
          ∑ j ∈ range (parametricInterval k m),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          (parametricInterval k m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*(parametricInterval k m : ℝ)^2 := by
  filter_upwards [eventually_parametric_small_prime_poly_rate k hk d (η/(14*(k : ℝ)+17)^d)
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
  have hlog : 0 ≤ 1+Real.log (parametricAmbient k m : ℝ) := by
    have hA : (1 : ℝ) ≤ parametricAmbient k m := by
      unfold parametricAmbient
      exact_mod_cast (Nat.one_le_pow _ _ (by decide : 1 ≤ 2))
    positivity [Real.log_nonneg hA]
  have hpow := pow_le_pow_left₀ hlog (parametric_ambient_log_le k m) d
  rw [mul_pow] at hpow
  have hsum : 0 ≤ (∑ q ∈ P, |(∑ i ∈ range (parametricInterval k m),
      ∑ j ∈ range (parametricInterval k m),
        if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
      (parametricInterval k m : ℝ)^2*q.totient/(q : ℝ)^2|) :=
    sum_nonneg (fun _ _ => abs_nonneg _)
  apply (mul_le_mul_of_nonneg_right hpow hsum).trans
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (14*(k : ℝ)+17)^d by positivity)
  convert hh using 1 <;> field_simp


/-- Bounded prime input, actual product support, a full-ambient above-half
modulus cutoff, and every fixed logarithmic saving, at each fixed k>=5. -/
theorem eventually_parametric_bounded_input_mean (k : ℕ) (hk : 5 ≤ k)
    (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^m < p ∧ p ≤ 2^(2*m) ∧
      parametricModulus k m^(14*k+16) = parametricAmbient k m^(8*k+4) ∧
      parametricAmbient k m+1 < parametricModulus k m^2 ∧
      (∀ a ∈ Icc 1 (parametricInterval k m), ∀ b ∈ Icc 1 (parametricInterval k m),
        a*b*p ≤ parametricAmbient k m) ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ parametricModulus k m) →
      (1+Real.log (parametricAmbient k m : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range (parametricInterval k m),
          ∑ j ∈ range (parametricInterval k m),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          (parametricInterval k m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*(parametricInterval k m : ℝ)^2 := by
  filter_upwards [eventually_parametric_successor_log_rate k (by omega) d η hη,
    eventually_ge_atTop 1] with m Hm hm
  obtain ⟨p,hp,hlo,hhi⟩ := exists_prime_in_smallPrimeInputRange m hm
  have htop : p ≤ 2^(2*m) := hhi
  refine ⟨p,hp,hlo,htop,parametric_ambient_power_relation k m,
    parametric_ambient_above_half k m hk hm,?_, Hm p hp hlo.le⟩
  intro a ha b hb
  exact parametric_rectangle_product_bound k m p a b htop (mem_Icc.mp ha).2 (mem_Icc.mp hb).2

/-- Every full-ambient level strictly below 4/7 is surpassed by one fixed
choice of parameters, with arbitrary fixed logarithmic savings. The
order of the quantifiers is retained: k precedes d, eta, and the scales.
This is a congruence mean, not a lower bound for prime successors. -/
theorem exists_bounded_input_mean_above_level (θ : ℝ) (hθ : θ < 4/7) :
    ∃ k : ℕ, 5 ≤ k ∧ θ < (8*(k : ℝ)+4)/(14*(k : ℝ)+16) ∧
      ∀ d : ℕ, ∀ η : ℝ, 0 < η →
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^m < p ∧ p ≤ 2^(2*m) ∧
      parametricModulus k m^(14*k+16) = parametricAmbient k m^(8*k+4) ∧
      parametricAmbient k m+1 < parametricModulus k m^2 ∧
      (parametricAmbient k m : ℝ)^θ < parametricModulus k m ∧
      (∀ a ∈ Icc 1 (parametricInterval k m), ∀ b ∈ Icc 1 (parametricInterval k m),
        a*b*p ≤ parametricAmbient k m) ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ parametricModulus k m) →
      (1+Real.log (parametricAmbient k m : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range (parametricInterval k m),
          ∑ j ∈ range (parametricInterval k m),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          (parametricInterval k m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*(parametricInterval k m : ℝ)^2 := by
  obtain ⟨k,hk,hlevel⟩ := exists_parametric_level_above θ hθ
  refine ⟨k,hk,hlevel,?_⟩
  intro d η hη
  filter_upwards [eventually_parametric_bounded_input_mean k hk d η hη,
    eventually_ge_atTop 1] with m Hm hm
  obtain ⟨p,hp,hlo,htop,hpower,hhalf,hbound,hmean⟩ := Hm
  exact ⟨p,hp,hlo,htop,hpower,hhalf,parametric_modulus_gt_rpow k m hm θ hlevel,hbound,hmean⟩

end Erdos821.AnalyticSieve
