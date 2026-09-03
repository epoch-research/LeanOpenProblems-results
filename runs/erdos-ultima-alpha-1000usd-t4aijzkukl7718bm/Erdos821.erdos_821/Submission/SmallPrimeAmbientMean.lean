import Submission.SquarefreePrimeInputMean
import Submission.CofactorMeanWithoutPrimeSuccessors

/-!
# An actual beyond-half ambient range with small prime inputs

For L=2^(64m) and input primes between 2^m and 2^(2m), all positive
rectangle products are at most A=2^(130m). The squarefree modulus cutoff
Q=2^(72m) satisfies Q^65=A^36, so its exponent is 36/65 relative to the
full product range, not merely relative to the free cofactors.

The result is a relative congruence mean, not a prime-successor supply.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman Erdos821.SuccessorAvoidance
set_option maxHeartbeats 3000000

noncomputable def smallPrimeInputTop (m : ℕ) : ℕ := 2^(2*m)
noncomputable def smallPrimeAmbientScale (m : ℕ) : ℕ :=
  smallPrimeInputTop m * rectangleIntervalScale m^2

lemma smallPrimeAmbientScale_eq (m : ℕ) : smallPrimeAmbientScale m = 2^(130*m) := by
  unfold smallPrimeAmbientScale smallPrimeInputTop rectangleIntervalScale
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

lemma smallPrimeAmbient_power_relation (m : ℕ) :
    rectangleModulusScale m^65 = smallPrimeAmbientScale m^36 := by
  rw [smallPrimeAmbientScale_eq]
  unfold rectangleModulusScale
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

lemma smallPrimeAmbient_above_half (m : ℕ) (hm : 1 ≤ m) :
    smallPrimeAmbientScale m+1 < rectangleModulusScale m^2 := by
  have hA : 1 < smallPrimeAmbientScale m := by
    rw [smallPrimeAmbientScale_eq]
    exact Nat.one_lt_pow (by omega) (by decide)
  have hdouble : 2*smallPrimeAmbientScale m ≤ rectangleModulusScale m^2 := by
    rw [smallPrimeAmbientScale_eq]
    unfold rectangleModulusScale
    rw [← pow_succ', ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

lemma smallPrime_rectangle_product_bound (m p a b : ℕ)
    (hp : p ≤ smallPrimeInputTop m)
    (ha : a ≤ rectangleIntervalScale m) (hb : b ≤ rectangleIntervalScale m) :
    a*b*p ≤ smallPrimeAmbientScale m := by
  have h := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hp
  convert h using 1
  unfold smallPrimeAmbientScale
  ring

lemma exists_prime_in_smallPrimeInputRange (m : ℕ) (hm : 1 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ 2^m < p ∧ p ≤ smallPrimeInputTop m := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2^m) (by positivity)
  refine ⟨p,hp,hlo,hhi.trans ?_⟩
  unfold smallPrimeInputTop
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The same large-scale threshold works for every prime p>=2^m.
In contrast with the older singleton statement, p need not exceed Q. -/
theorem eventually_small_prime_input_rectangle_mean (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → 2^m ≤ p →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
        (∑ q ∈ P, |doubleCofactorRow q (u q) p 1 1
          (rectangleIntervalScale m) (rectangleIntervalScale m)-
          (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
            η*(rectangleIntervalScale m : ℝ)^2 := by
  filter_upwards [eventually_doubleCofactor_small_prime_relative η hη] with m hm
  intro p hp hlo P hP u
  have hs : ∀ n, singletonPrimeWeight p hp n ≠ 0 → n.Prime ∧ 2^m ≤ n := by
    intro n hn
    rw [singletonPrimeWeight_support p hp n hn]
    exact ⟨hp,hlo⟩
  have h := hm (singletonPrimeWeight p hp) (singletonPrimeWeight_nonneg p hp)
    hs P hP p 1 1 u
  simpa only [singletonPrimeWeight_cofactor, squarefreeCofactorMain,
    singletonPrimeWeight_mass, mul_one, sq] using h

/-- The range is nonvacuous at every sufficiently large scale. All counted
products have the declared full ambient bound. No primality of those
products plus one is asserted. -/
theorem eventually_exists_prime_ambient_rectangle_mean (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^m < p ∧ p ≤ smallPrimeInputTop m ∧
      rectangleModulusScale m^65 = smallPrimeAmbientScale m^36 ∧
      smallPrimeAmbientScale m+1 < rectangleModulusScale m^2 ∧
      (∀ a ∈ Icc 1 (rectangleIntervalScale m), ∀ b ∈ Icc 1 (rectangleIntervalScale m),
        a*b*p ≤ smallPrimeAmbientScale m) ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
        (∑ q ∈ P, |doubleCofactorRow q (u q) p 1 1
          (rectangleIntervalScale m) (rectangleIntervalScale m)-
          (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
            η*(rectangleIntervalScale m : ℝ)^2 := by
  filter_upwards [eventually_small_prime_input_rectangle_mean η hη, eventually_ge_atTop 1]
    with m Hm hm
  obtain ⟨p,hp,hlo,hhi⟩ := exists_prime_in_smallPrimeInputRange m hm
  refine ⟨p,hp,hlo,hhi,smallPrimeAmbient_power_relation m,smallPrimeAmbient_above_half m hm,?_,
    Hm p hp hlo.le⟩
  intro a ha b hb
  exact smallPrime_rectangle_product_bound m p a b hhi (mem_Icc.mp ha).2 (mem_Icc.mp hb).2

lemma doubleCofactorRow_neg_one_natural (q p B C : ℕ) :
    doubleCofactorRow q (-1) p 1 1 B C =
      ∑ i ∈ range B, ∑ j ∈ range C,
        if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0 := by
  unfold doubleCofactorRow
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  have he : ((↑(-1 : (ZMod q)ˣ) : ZMod q)*((1+i : ℤ) : ZMod q)*
      ((1+j : ℤ) : ZMod q)*(p : ZMod q)=1) ↔ q ∣ (i+1)*(j+1)*p+1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor <;> intro h <;> linear_combination -h
  simp only [he]

/-- The estimate expressed as actual natural-number divisibility of
successors, rather than as a ZMod row. It is not a primality statement. -/
theorem eventually_small_prime_successor_divisibility_mean (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → 2^m ≤ p →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
        (∑ q ∈ P, |(∑ i ∈ range (rectangleIntervalScale m),
          ∑ j ∈ range (rectangleIntervalScale m),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
            η*(rectangleIntervalScale m : ℝ)^2 := by
  filter_upwards [eventually_small_prime_input_rectangle_mean η hη] with m hm
  intro p hp hlo P hP
  simpa only [doubleCofactorRow_neg_one_natural] using hm p hp hlo P hP (fun _ => -1)

end Erdos821.AnalyticSieve
