import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_206 : 3 ≤ primes 206 ∧ primes 206 ≤ 2503 ∧
    Row (primes 206) (states 206) (states 207) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
