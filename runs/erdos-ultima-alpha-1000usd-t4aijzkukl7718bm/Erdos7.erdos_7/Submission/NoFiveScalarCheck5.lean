import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_5 : 3 ≤ primes 5 ∧ primes 5 ≤ 2503 ∧
    Row (primes 5) (states 5) (states 6) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
