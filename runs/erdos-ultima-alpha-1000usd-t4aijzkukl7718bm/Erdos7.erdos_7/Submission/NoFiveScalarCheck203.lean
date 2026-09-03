import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_203 : 3 ≤ primes 203 ∧ primes 203 ≤ 2503 ∧
    Row (primes 203) (states 203) (states 204) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
