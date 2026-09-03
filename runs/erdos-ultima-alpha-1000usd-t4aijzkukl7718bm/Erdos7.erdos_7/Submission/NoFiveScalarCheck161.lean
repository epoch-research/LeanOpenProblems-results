import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_161 : 3 ≤ primes 161 ∧ primes 161 ≤ 2503 ∧
    Row (primes 161) (states 161) (states 162) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
