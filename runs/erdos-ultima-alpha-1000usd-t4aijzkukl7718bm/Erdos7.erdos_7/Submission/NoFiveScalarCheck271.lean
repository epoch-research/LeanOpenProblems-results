import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_271 : 3 ≤ primes 271 ∧ primes 271 ≤ 2503 ∧
    Row (primes 271) (states 271) (states 272) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
