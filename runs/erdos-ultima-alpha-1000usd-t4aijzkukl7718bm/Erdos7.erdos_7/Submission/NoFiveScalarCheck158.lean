import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_158 : 3 ≤ primes 158 ∧ primes 158 ≤ 2503 ∧
    Row (primes 158) (states 158) (states 159) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
