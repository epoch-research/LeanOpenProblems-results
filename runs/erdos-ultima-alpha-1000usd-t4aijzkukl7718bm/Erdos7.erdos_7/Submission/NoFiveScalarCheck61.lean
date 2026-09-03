import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_61 : 3 ≤ primes 61 ∧ primes 61 ≤ 2503 ∧
    Row (primes 61) (states 61) (states 62) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
