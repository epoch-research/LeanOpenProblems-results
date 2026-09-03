import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_312 : 3 ≤ primes 312 ∧ primes 312 ≤ 2503 ∧
    Row (primes 312) (states 312) (states 313) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
