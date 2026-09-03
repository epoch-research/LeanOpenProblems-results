import Submission.SmallPrimeMeanRate

/-! Independent expanded-type and axiom checks for the quantitative rates. -/
open Nat Finset ArithmeticFunction Filter
open scoped BigOperators Topology
open Erdos821.AnalyticSieve Erdos821.Kloosterman

example : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ f : ArithmeticFunction ℝ,
    (∀ n, 0 ≤ f n) → (∀ n, f n ≠ 0 → n.Prime ∧ 2^m ≤ n) →
    ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ 2^(72*m)) →
    ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
    (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N (2^(64*m)) (2^(64*m)) X-
      ((2^(64*m) : ℕ) : ℝ)*((2^(64*m) : ℕ) : ℝ)*q.totient/(q : ℝ)^2*
        (∑ n ∈ Icc 1 X, f n)|) ≤
      (C*((m : ℝ)+1)^2/(2 : ℝ)^m)*((2^(64*m) : ℕ) : ℝ)^2*
        (∑ n ∈ Icc 1 X, f n) := by
  simpa only [rectangleIntervalScale, rectangleModulusScale, squarefreeCofactorMain,
    restrictedMass] using exists_doubleCofactor_small_prime_rate

example (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^m < p ∧ p ≤ 2^(2*m) ∧
      (2^(72*m) : ℕ)^65 = (2^(130*m) : ℕ)^36 ∧
      2^(130*m)+1 < (2^(72*m) : ℕ)^2 ∧
      (∀ a ∈ Icc 1 (2^(64*m)), ∀ b ∈ Icc 1 (2^(64*m)), a*b*p ≤ 2^(130*m)) ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ 2^(72*m)) →
      (1+Real.log ((2^(130*m) : ℕ) : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range (2^(64*m)), ∑ j ∈ range (2^(64*m)),
          if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
            ((2^(64*m) : ℕ) : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*((2^(64*m) : ℕ) : ℝ)^2 := by
  simpa only [smallPrimeAmbientScale_eq, smallPrimeInputTop, rectangleIntervalScale,
    rectangleModulusScale] using eventually_exists_prime_successor_log_rate d η hη

#print axioms Erdos821.Kloosterman.squarefree_rectangle_kernel_rate
#print axioms Erdos821.Kloosterman.rectangle_prime_nonunit_rate
#print axioms Erdos821.AnalyticSieve.exists_doubleCofactor_small_prime_rate
#print axioms Erdos821.AnalyticSieve.eventually_doubleCofactor_small_prime_poly_rate
#print axioms Erdos821.AnalyticSieve.smallPrimeAmbientScale_log_le
#print axioms Erdos821.AnalyticSieve.eventually_small_prime_successor_log_rate
#print axioms Erdos821.AnalyticSieve.eventually_exists_prime_successor_log_rate
