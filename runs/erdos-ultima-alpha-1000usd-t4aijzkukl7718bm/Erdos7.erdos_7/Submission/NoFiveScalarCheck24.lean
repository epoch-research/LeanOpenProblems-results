import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_24 : 3 ≤ primes 24 ∧ primes 24 ≤ 2503 ∧
    Row (primes 24) (states 24) (states 25) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
