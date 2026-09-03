import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_10 : 3 ≤ primes 10 ∧ primes 10 ≤ 2503 ∧
    Row (primes 10) (states 10) (states 11) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
