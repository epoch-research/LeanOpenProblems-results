import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_362 : 3 ≤ primes 362 ∧ primes 362 ≤ 2503 ∧
    Row (primes 362) (states 362) (states 363) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
