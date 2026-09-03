import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_32 : 3 ≤ primes 32 ∧ primes 32 ≤ 2503 ∧
    Row (primes 32) (states 32) (states 33) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
