import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_286 : 3 ≤ primes 286 ∧ primes 286 ≤ 2503 ∧
    Row (primes 286) (states 286) (states 287) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
