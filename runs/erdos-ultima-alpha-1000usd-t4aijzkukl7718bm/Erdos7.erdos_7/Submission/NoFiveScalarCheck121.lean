import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_121 : 3 ≤ primes 121 ∧ primes 121 ≤ 2503 ∧
    Row (primes 121) (states 121) (states 122) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
