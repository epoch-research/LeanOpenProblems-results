import Submission.SquarefreeCofactorScales

/-! Independent axiom and expanded-type checks of the squarefree cofactor mean. -/
#print axioms Erdos821.Kloosterman.ringKloosterman_equiv
#print axioms Erdos821.Kloosterman.ringKloosterman_norm_le_card
#print axioms Erdos821.Kloosterman.primitive_transport
#print axioms Erdos821.Kloosterman.ringKloosterman_eq
#print axioms Erdos821.Kloosterman.ringKloosterman_fourth_field
#print axioms Erdos821.Kloosterman.coordinateChar_apply
#print axioms Erdos821.Kloosterman.primitive_coordinate
#print axioms Erdos821.Kloosterman.character_pi_factorization
#print axioms Erdos821.Kloosterman.ringKloosterman_pi
#print axioms Erdos821.Kloosterman.ringKloosterman_pi_fourth
#print axioms Erdos821.Kloosterman.squarefreeCRT_apply
#print axioms Erdos821.Kloosterman.annihilatorPrimeProduct_dvd_gcd
#print axioms Erdos821.Kloosterman.annihilatorPrimeProduct_le_gcd
#print axioms Erdos821.Kloosterman.ringKloosterman_squarefree_fourth
#print axioms Erdos821.Kloosterman.ringFourier_inversion
#print axioms Erdos821.Kloosterman.ringWeightedKloosterman_completion
#print axioms Erdos821.Kloosterman.ringWeightedKloosterman_norm_le_of_bound
#print axioms Erdos821.Kloosterman.ringFourier_zero
#print axioms Erdos821.Kloosterman.ringWeightedKloosterman_zero
#print axioms Erdos821.Kloosterman.ringHyperbolaWeight_completion
#print axioms Erdos821.Kloosterman.ringHyperbolaWeight_error_identity
#print axioms Erdos821.Kloosterman.ringHyperbolaWeight_error_norm_le
#print axioms Erdos821.Kloosterman.squarefreeBound_nonneg
#print axioms Erdos821.Kloosterman.squarefreeBound_fourth
#print axioms Erdos821.Kloosterman.ringKloosterman_squarefree_norm
#print axioms Erdos821.Kloosterman.gcd_reciprocal_sum_le
#print axioms Erdos821.Kloosterman.gcd_reciprocal_reflect_sum
#print axioms Erdos821.Kloosterman.ring_intervalResidueWeight_pairing
#print axioms Erdos821.Kloosterman.ringFourier_intervalResidueWeight
#print axioms Erdos821.Kloosterman.ring_intervalResidueWeight_mass
#print axioms Erdos821.Kloosterman.sum_nonzero_residue_values
#print axioms Erdos821.Kloosterman.sum_nonzero_residue_neg
#print axioms Erdos821.Kloosterman.gcd_val_neg
#print axioms Erdos821.Kloosterman.gcd_val_mul_unit
#print axioms Erdos821.Kloosterman.nonzero_ringFourierMass_interval_le
#print axioms Erdos821.Kloosterman.ringFourierMass_interval_le
#print axioms Erdos821.Kloosterman.gcd_ringFourierMass_interval_le
#print axioms Erdos821.Kloosterman.ringWeightedKloosterman_interval_norm
#print axioms Erdos821.Kloosterman.squarefree_interval_hyperbola_error
#print axioms Erdos821.Kloosterman.ring_unit_interval_pairing
#print axioms Erdos821.Kloosterman.ringUnitMass_interval
#print axioms Erdos821.Kloosterman.ringHyperbolaWeight_eq_rectangleCount
#print axioms Erdos821.Kloosterman.ringRectangleCount_error_units
#print axioms Erdos821.Kloosterman.ringIntervalUnitCount_eq_coprime
#print axioms Erdos821.Kloosterman.ringIntervalUnitCount_density_error
#print axioms Erdos821.Kloosterman.ringRectangleCount_error_local
#print axioms Erdos821.Kloosterman.squarefreeBound_le_primeFactor_multiple
#print axioms Erdos821.Kloosterman.squarefreeBound_divisor_factor
#print axioms Erdos821.Kloosterman.squarefreeRectangleError_le
#print axioms Erdos821.Kloosterman.exists_uniform_six_primeFactor_bound
#print axioms Erdos821.Kloosterman.sum_squarefreeRectangleError_le
#print axioms Erdos821.AnalyticSieve.unit_squarefree_doubleRow_eq
#print axioms Erdos821.AnalyticSieve.squarefree_doubleCofactorRow_error
#print axioms Erdos821.AnalyticSieve.squarefree_doubleCofactorWeight_error
#print axioms Erdos821.AnalyticSieve.doubleCofactor_squarefree_modulus_mean
#print axioms Erdos821.Kloosterman.rectangleModulusScale_small_rpow
#print axioms Erdos821.Kloosterman.eventually_squarefree_rectangle_kernel_relative
#print axioms Erdos821.AnalyticSieve.eventually_doubleCofactor_squarefree_relative
#print axioms Erdos821.AnalyticSieve.eventually_doubleCofactor_squarefree_prime_weight

open Finset Filter
open scoped BigOperators Classical Topology
open Erdos821.Kloosterman Erdos821.AnalyticSieve
example (q : ℕ) [NeZero q] (hq : Squarefree q)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (a b : ZMod q) :
    ‖ringKloosterman ψ a b‖^4 ≤
      (3 : ℝ)^q.primeFactors.card*(q : ℝ)^3*(Nat.gcd b.val q : ℕ) :=
  ringKloosterman_squarefree_fourth q hq ψ hψ a b
example (q : ℕ) [NeZero q] (hq : Squarefree q)
    (M N : ℤ) (B C : ℕ) (r : (ZMod q)ˣ) :
    |(ringRectangleCount q M N B C r : ℝ)-(B : ℝ)*C*q.totient/(q : ℝ)^2| ≤
      squarefreeRectangleError q B C := ringRectangleCount_error_local hq M N B C r
example (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ, (∀ n, 0 ≤ f n) →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ X : ℕ, (∀ q ∈ P, ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime q) →
      ∀ M N : ℤ, ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
      (∑ q ∈ P, |doubleCofactorWeight f q (u q) M N
        (rectangleIntervalScale m) (rectangleIntervalScale m) X-
          squarefreeCofactorMain f q (rectangleIntervalScale m) (rectangleIntervalScale m) X|) ≤
        η*(rectangleIntervalScale m : ℝ)^2*restrictedMass f X :=
  eventually_doubleCofactor_squarefree_relative η hη
