import Submission.NoFiveScalarSoundness
import Submission.NoFiveScalarCertificate

/-! The checked scalar table bounds the finite-exponent prefix cost. -/
namespace Erdos7NoFiveScalar
open Erdos7CompressionSieve

theorem prefix_cost_bound (E : Fin 366 → ℕ) :
    exponentCost E (tails E) (fun i => cap (primes i)) (fun i => 1/(primes i-1 : ℚ)) ≤
      (states 0).eval 1 :=
  prefix_cost_bound_of_certificate certificate E

#print axioms prefix_cost_bound
end Erdos7NoFiveScalar
