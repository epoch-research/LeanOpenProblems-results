import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_356 : 3 ≤ primes 356 ∧ primes 356 ≤ 2503 ∧
    Row (primes 356) (states 356) (states 357) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
