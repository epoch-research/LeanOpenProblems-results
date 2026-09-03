import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_326 : 3 ≤ primes 326 ∧ primes 326 ≤ 2503 ∧
    Row (primes 326) (states 326) (states 327) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
