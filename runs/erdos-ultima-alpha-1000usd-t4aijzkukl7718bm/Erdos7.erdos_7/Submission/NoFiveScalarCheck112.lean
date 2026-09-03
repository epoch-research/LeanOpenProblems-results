import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_112 : 3 ≤ primes 112 ∧ primes 112 ≤ 2503 ∧
    Row (primes 112) (states 112) (states 113) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
