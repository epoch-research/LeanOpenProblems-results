import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_11 : 3 ≤ primes 11 ∧ primes 11 ≤ 2503 ∧
    Row (primes 11) (states 11) (states 12) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
