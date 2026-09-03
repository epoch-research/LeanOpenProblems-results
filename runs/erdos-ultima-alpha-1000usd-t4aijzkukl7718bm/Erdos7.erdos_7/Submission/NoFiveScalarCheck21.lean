import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_21 : 3 ≤ primes 21 ∧ primes 21 ≤ 2503 ∧
    Row (primes 21) (states 21) (states 22) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
