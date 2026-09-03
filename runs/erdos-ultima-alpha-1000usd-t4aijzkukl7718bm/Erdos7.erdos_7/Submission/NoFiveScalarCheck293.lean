import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_293 : 3 ≤ primes 293 ∧ primes 293 ≤ 2503 ∧
    Row (primes 293) (states 293) (states 294) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
