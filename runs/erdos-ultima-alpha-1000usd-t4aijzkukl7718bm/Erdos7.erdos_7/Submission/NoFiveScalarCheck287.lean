import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_287 : 3 ≤ primes 287 ∧ primes 287 ≤ 2503 ∧
    Row (primes 287) (states 287) (states 288) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
