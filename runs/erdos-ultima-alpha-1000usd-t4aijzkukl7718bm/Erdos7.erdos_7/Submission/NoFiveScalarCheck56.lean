import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_56 : 3 ≤ primes 56 ∧ primes 56 ≤ 2503 ∧
    Row (primes 56) (states 56) (states 57) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
