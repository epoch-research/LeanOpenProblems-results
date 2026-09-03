import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_357 : 3 ≤ primes 357 ∧ primes 357 ≤ 2503 ∧
    Row (primes 357) (states 357) (states 358) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
