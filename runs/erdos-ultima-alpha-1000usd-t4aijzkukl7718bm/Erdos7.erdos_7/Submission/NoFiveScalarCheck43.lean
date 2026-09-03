import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_43 : 3 ≤ primes 43 ∧ primes 43 ≤ 2503 ∧
    Row (primes 43) (states 43) (states 44) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
