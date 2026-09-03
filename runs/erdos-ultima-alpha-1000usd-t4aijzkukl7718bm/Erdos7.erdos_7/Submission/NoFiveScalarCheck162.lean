import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_162 : 3 ≤ primes 162 ∧ primes 162 ≤ 2503 ∧
    Row (primes 162) (states 162) (states 163) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
