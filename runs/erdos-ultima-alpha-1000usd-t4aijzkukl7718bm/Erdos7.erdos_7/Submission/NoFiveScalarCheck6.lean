import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_6 : 3 ≤ primes 6 ∧ primes 6 ≤ 2503 ∧
    Row (primes 6) (states 6) (states 7) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
