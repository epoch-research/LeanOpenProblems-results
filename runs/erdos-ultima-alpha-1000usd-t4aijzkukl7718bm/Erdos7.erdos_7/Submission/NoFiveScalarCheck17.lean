import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_17 : 3 ≤ primes 17 ∧ primes 17 ≤ 2503 ∧
    Row (primes 17) (states 17) (states 18) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
