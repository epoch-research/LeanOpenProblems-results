import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_64 : 3 ≤ primes 64 ∧ primes 64 ≤ 2503 ∧
    Row (primes 64) (states 64) (states 65) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
