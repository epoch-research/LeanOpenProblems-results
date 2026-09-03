import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_325 : 3 ≤ primes 325 ∧ primes 325 ≤ 2503 ∧
    Row (primes 325) (states 325) (states 326) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
