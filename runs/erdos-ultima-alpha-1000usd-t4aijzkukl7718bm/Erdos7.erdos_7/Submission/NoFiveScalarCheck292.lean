import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_292 : 3 ≤ primes 292 ∧ primes 292 ≤ 2503 ∧
    Row (primes 292) (states 292) (states 293) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
