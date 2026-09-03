import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_55 : 3 ≤ primes 55 ∧ primes 55 ≤ 2503 ∧
    Row (primes 55) (states 55) (states 56) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
