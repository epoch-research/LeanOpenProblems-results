import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_42 : 3 ≤ primes 42 ∧ primes 42 ≤ 2503 ∧
    Row (primes 42) (states 42) (states 43) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
