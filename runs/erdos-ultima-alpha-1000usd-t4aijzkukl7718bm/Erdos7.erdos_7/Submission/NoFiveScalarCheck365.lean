import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_365 : 3 ≤ primes 365 ∧ primes 365 ≤ 2503 ∧
    Row (primes 365) (states 365) (states 366) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
