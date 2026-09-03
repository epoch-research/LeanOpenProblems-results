import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_156 : 3 ≤ primes 156 ∧ primes 156 ≤ 2503 ∧
    Row (primes 156) (states 156) (states 157) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
