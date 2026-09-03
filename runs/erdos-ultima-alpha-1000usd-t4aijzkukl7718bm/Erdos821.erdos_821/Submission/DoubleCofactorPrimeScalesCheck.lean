import Submission.DoubleCofactorPrimeScales
/-! Axiom checks for the new two-cofactor prime-modulus mean. -/
#print axioms Erdos821.Kloosterman.fieldFourier_zero
#print axioms Erdos821.Kloosterman.weightedKloosterman_zero
#print axioms Erdos821.Kloosterman.hyperbolaWeight_completion
#print axioms Erdos821.Kloosterman.hyperbolaWeight_error_identity
#print axioms Erdos821.Kloosterman.hyperbolaWeight_error_norm_le
#print axioms Erdos821.Kloosterman.intervalResidueWeight_mass
#print axioms Erdos821.Kloosterman.nonzero_fourierMass_interval_le
#print axioms Erdos821.Kloosterman.interval_hyperbola_error_le
#print axioms Erdos821.Kloosterman.unit_intervalResidueWeight_pairing
#print axioms Erdos821.Kloosterman.unitMass_intervalResidueWeight
#print axioms Erdos821.Kloosterman.hyperbolaWeight_eq_rectangleCount
#print axioms Erdos821.Kloosterman.rectangleCount_error_units
#print axioms Erdos821.Kloosterman.intervalUnitCount_error
#print axioms Erdos821.Kloosterman.rectangleCount_error_local
#print axioms Erdos821.AnalyticSieve.unit_doubleCofactorRow_eq
#print axioms Erdos821.AnalyticSieve.unit_doubleCofactorRow_error
#print axioms Erdos821.AnalyticSieve.doubleCofactorWeight_error
#print axioms Erdos821.Kloosterman.modulusBound_nonneg
#print axioms Erdos821.Kloosterman.modulusBound_fourth
#print axioms Erdos821.Kloosterman.modulusBound_mono
#print axioms Erdos821.Kloosterman.harmonic_cast_mono
#print axioms Erdos821.Kloosterman.sum_fourth_le_card_cube
#print axioms Erdos821.Kloosterman.sum_modulusBound_div_fourth
#print axioms Erdos821.Kloosterman.sum_modulusBound_div_le
#print axioms Erdos821.Kloosterman.sum_modulusBound_le
#print axioms Erdos821.Kloosterman.rectangleError_nonneg
#print axioms Erdos821.Kloosterman.sum_rectangleError_le
#print axioms Erdos821.AnalyticSieve.doubleCofactor_prime_modulus_mean
#print axioms Erdos821.Kloosterman.modulusBound_power_four
#print axioms Erdos821.Kloosterman.harmonic_two_pow_le
#print axioms Erdos821.Kloosterman.rectangleScale_power_relation
#print axioms Erdos821.Kloosterman.rectangleIntervalScale_lt_modulus
#print axioms Erdos821.Kloosterman.rectangleMeanKernel_scale_bound
#print axioms Erdos821.Kloosterman.eventually_rectangleMeanKernel_relative
#print axioms Erdos821.AnalyticSieve.eventually_doubleCofactor_prime_relative
#print axioms Erdos821.AnalyticSieve.eventually_doubleCofactor_prime_subset
open Erdos821.Kloosterman
example (m : ℕ) : rectangleModulusScale m ^ 16 = (rectangleIntervalScale m ^ 2)^9 :=
  rectangleScale_power_relation m
example (m : ℕ) (hm : 1 ≤ m) : rectangleIntervalScale m < rectangleModulusScale m :=
  rectangleIntervalScale_lt_modulus m hm
open Filter
open scoped Topology
example (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      rectangleMeanKernel (rectangleModulusScale m) (rectangleIntervalScale m) (rectangleIntervalScale m) ≤
        η*(rectangleIntervalScale m : ℝ)^2 :=
  eventually_rectangleMeanKernel_relative η hη
