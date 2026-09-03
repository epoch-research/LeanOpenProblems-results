import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_31 : 3 ≤ primes 31 ∧ primes 31 ≤ 2503 ∧
    Row (primes 31) (states 31) (states 32) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
