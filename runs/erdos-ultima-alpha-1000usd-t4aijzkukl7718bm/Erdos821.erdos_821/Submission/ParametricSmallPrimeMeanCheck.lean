import Submission.ParametricSmallPrimeMean

/-! Expanded-type and axiom audit for parametric means below level 4/7. -/
open Nat Finset ArithmeticFunction Filter
open scoped BigOperators Topology
open Erdos821.AnalyticSieve Erdos821.Kloosterman

example (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      (∀ n, f n ≠ 0 → n.Prime ∧ 2^m ≤ n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ (2^((8*k+4)*m) : ℕ)) →
      ∀ X : ℕ, ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        ((2^((7*k+7)*m) : ℕ)) ((2^((7*k+7)*m) : ℕ)) X-
        squarefreeCofactorMain f q ((2^((7*k+7)*m) : ℕ)) ((2^((7*k+7)*m) : ℕ)) X|) ≤
      (C*((m : ℝ)+1)^2/(2 : ℝ)^m)*((2^((7*k+7)*m) : ℕ) : ℝ)^2*(∑ n ∈ Icc 1 X, f n) := by
  simpa only [parametricInterval, parametricModulus, squarefreeCofactorMain, restrictedMass] using exists_parametric_small_prime_rate k hk

example (θ : ℝ) (hθ : θ < 4/7) :
    ∃ k : ℕ, 5 ≤ k ∧ θ < (8*(k : ℝ)+4)/(14*(k : ℝ)+16) ∧
      ∀ d : ℕ, ∀ η : ℝ, 0 < η →
    ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^m < p ∧ p ≤ 2^(2*m) ∧
      (2^((8*k+4)*m) : ℕ)^(14*k+16) = (2^((14*k+16)*m) : ℕ)^(8*k+4) ∧
      (2^((14*k+16)*m) : ℕ)+1 < (2^((8*k+4)*m) : ℕ)^2 ∧
      ((2^((14*k+16)*m) : ℕ) : ℝ)^θ < (2^((8*k+4)*m) : ℕ) ∧
      (∀ a ∈ Icc 1 ((2^((7*k+7)*m) : ℕ)), ∀ b ∈ Icc 1 ((2^((7*k+7)*m) : ℕ)),
        a*b*p ≤ (2^((14*k+16)*m) : ℕ)) ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ (2^((8*k+4)*m) : ℕ)) →
      (1+Real.log ((2^((14*k+16)*m) : ℕ) : ℝ))^d*
        (∑ q ∈ P, |(∑ i ∈ range ((2^((7*k+7)*m) : ℕ)),
          ∑ j ∈ range ((2^((7*k+7)*m) : ℕ)),
            if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
          ((2^((7*k+7)*m) : ℕ) : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
        η*((2^((7*k+7)*m) : ℕ) : ℝ)^2 := by
  simpa only [parametricInterval, parametricModulus, parametricAmbient] using exists_bounded_input_mean_above_level θ hθ

#print axioms Erdos821.Kloosterman.parametricInterval
#print axioms Erdos821.Kloosterman.parametricModulus
#print axioms Erdos821.Kloosterman.parametricAmbient
#print axioms Erdos821.Kloosterman.parametric_harmonic_bound
#print axioms Erdos821.Kloosterman.parametric_rectangle_kernel
#print axioms Erdos821.Kloosterman.parametric_modulus_small_rpow
#print axioms Erdos821.Kloosterman.parametric_rectangle_kernel_rate
#print axioms Erdos821.Kloosterman.parametric_nonunit_rate
#print axioms Erdos821.Kloosterman.parametric_ambient_power_relation
#print axioms Erdos821.Kloosterman.parametric_ambient_above_half
#print axioms Erdos821.Kloosterman.parametric_rectangle_product_bound
#print axioms Erdos821.Kloosterman.parametric_ambient_log_le
#print axioms Erdos821.Kloosterman.parametric_level_lt_four_sevenths
#print axioms Erdos821.Kloosterman.exists_parametric_level_above
#print axioms Erdos821.Kloosterman.parametric_modulus_eq_rpow
#print axioms Erdos821.Kloosterman.parametric_modulus_gt_rpow
#print axioms Erdos821.AnalyticSieve.exists_parametric_small_prime_rate
#print axioms Erdos821.AnalyticSieve.eventually_parametric_small_prime_poly_rate
#print axioms Erdos821.AnalyticSieve.eventually_parametric_successor_log_rate
#print axioms Erdos821.AnalyticSieve.eventually_parametric_bounded_input_mean
#print axioms Erdos821.AnalyticSieve.exists_bounded_input_mean_above_level
