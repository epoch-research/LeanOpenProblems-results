import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_355 : 3 ≤ primes 355 ∧ primes 355 ≤ 2503 ∧
    Row (primes 355) (states 355) (states 356) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
