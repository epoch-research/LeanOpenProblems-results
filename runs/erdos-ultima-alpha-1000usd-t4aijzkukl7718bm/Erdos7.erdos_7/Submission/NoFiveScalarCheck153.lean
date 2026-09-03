import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_153 : 3 ≤ primes 153 ∧ primes 153 ≤ 2503 ∧
    Row (primes 153) (states 153) (states 154) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
