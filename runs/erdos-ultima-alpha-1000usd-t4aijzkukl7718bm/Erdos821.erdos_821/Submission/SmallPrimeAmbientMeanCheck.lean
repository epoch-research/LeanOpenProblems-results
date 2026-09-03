import Submission.SmallPrimeAmbientMean

/-! Expanded-type and axiom checks for nonunit and small-prime ambient means. -/

open Nat Finset ArithmeticFunction Filter
open scoped BigOperators Topology
open Erdos821.AnalyticSieve Erdos821.Kloosterman

example (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ 2^(72*m)) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N (2^(64*m)) (2^(64*m)) X-
        ((2^(64*m) : ℕ) : ℝ)*((2^(64*m) : ℕ) : ℝ)*q.totient/(q : ℝ)^2*
          (∑ n ∈ Icc 1 X, if n.Coprime q then f n else 0)|) ≤
        η*((2^(64*m) : ℕ) : ℝ)^2*restrictedMass f X := by
  simpa only [rectangleIntervalScale, rectangleModulusScale, squarefreeCofactorUnitMain,
    restrictedUnitMass, restrictedMass, unitRestrictedWeight, ArithmeticFunction.coe_mk]
    using eventually_doubleCofactor_squarefree_nonunit_relative η hη

example (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → 2^m ≤ p →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ 2^(72*m)) →
      (∑ q ∈ P, |(∑ i ∈ range (2^(64*m)), ∑ j ∈ range (2^(64*m)),
        if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
        ((2^(64*m) : ℕ) : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
          η*((2^(64*m) : ℕ) : ℝ)^2 := by
  simpa only [rectangleIntervalScale, rectangleModulusScale]
    using eventually_small_prime_successor_divisibility_mean η hη

example (m : ℕ) : (2^(72*m) : ℕ)^65 = (2^(130*m) : ℕ)^36 := by
  simpa only [rectangleModulusScale, smallPrimeAmbientScale_eq]
    using smallPrimeAmbient_power_relation m

example (m : ℕ) (hm : 1 ≤ m) : 2^(130*m)+1 < (2^(72*m) : ℕ)^2 := by
  simpa only [rectangleModulusScale, smallPrimeAmbientScale_eq]
    using smallPrimeAmbient_above_half m hm

#print axioms Erdos821.AnalyticSieve.unitRestrictedWeight
#print axioms Erdos821.AnalyticSieve.unitRestrictedWeight_nonneg
#print axioms Erdos821.AnalyticSieve.unitRestrictedWeight_support
#print axioms Erdos821.AnalyticSieve.restrictedUnitMass
#print axioms Erdos821.AnalyticSieve.restrictedUnitMass_eq_sub
#print axioms Erdos821.AnalyticSieve.restrictedUnitMass_nonneg
#print axioms Erdos821.AnalyticSieve.restrictedUnitMass_le
#print axioms Erdos821.AnalyticSieve.nonunit_doubleCofactorRow_zero
#print axioms Erdos821.AnalyticSieve.doubleCofactorWeight_unitRestriction
#print axioms Erdos821.AnalyticSieve.squarefreeCofactorUnitMain
#print axioms Erdos821.AnalyticSieve.squarefree_doubleCofactorWeight_unit_error
#print axioms Erdos821.AnalyticSieve.squarefreeRectangleError_nonneg
#print axioms Erdos821.AnalyticSieve.doubleCofactor_squarefree_nonunit_mean
#print axioms Erdos821.AnalyticSieve.eventually_doubleCofactor_squarefree_nonunit_relative
#print axioms Erdos821.AnalyticSieve.squarefreeCofactor_main_difference
#print axioms Erdos821.AnalyticSieve.squarefreeCofactor_main_difference_le
#print axioms Erdos821.AnalyticSieve.squarefreeCofactor_prime_main_correction
#print axioms Erdos821.AnalyticSieve.doubleCofactor_squarefree_prime_mean
#print axioms Erdos821.AnalyticSieve.eventually_rectangle_prime_nonunit_coefficient
#print axioms Erdos821.AnalyticSieve.eventually_doubleCofactor_small_prime_relative
#print axioms Erdos821.AnalyticSieve.smallPrimeInputTop
#print axioms Erdos821.AnalyticSieve.smallPrimeAmbientScale
#print axioms Erdos821.AnalyticSieve.smallPrimeAmbientScale_eq
#print axioms Erdos821.AnalyticSieve.smallPrimeAmbient_power_relation
#print axioms Erdos821.AnalyticSieve.smallPrimeAmbient_above_half
#print axioms Erdos821.AnalyticSieve.smallPrime_rectangle_product_bound
#print axioms Erdos821.AnalyticSieve.exists_prime_in_smallPrimeInputRange
#print axioms Erdos821.AnalyticSieve.eventually_small_prime_input_rectangle_mean
#print axioms Erdos821.AnalyticSieve.eventually_exists_prime_ambient_rectangle_mean
#print axioms Erdos821.AnalyticSieve.doubleCofactorRow_neg_one_natural
#print axioms Erdos821.AnalyticSieve.eventually_small_prime_successor_divisibility_mean
