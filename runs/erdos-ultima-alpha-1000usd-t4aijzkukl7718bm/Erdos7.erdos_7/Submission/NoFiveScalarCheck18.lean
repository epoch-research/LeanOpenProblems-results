import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_18 : 3 ≤ primes 18 ∧ primes 18 ≤ 2503 ∧
    Row (primes 18) (states 18) (states 19) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
