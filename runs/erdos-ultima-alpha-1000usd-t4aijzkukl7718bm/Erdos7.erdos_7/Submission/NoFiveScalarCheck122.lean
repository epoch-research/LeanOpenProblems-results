import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_122 : 3 ≤ primes 122 ∧ primes 122 ≤ 2503 ∧
    Row (primes 122) (states 122) (states 123) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
