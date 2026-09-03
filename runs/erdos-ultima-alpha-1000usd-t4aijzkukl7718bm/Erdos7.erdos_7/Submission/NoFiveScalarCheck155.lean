import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_155 : 3 ≤ primes 155 ∧ primes 155 ≤ 2503 ∧
    Row (primes 155) (states 155) (states 156) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
