import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_8 : 3 ≤ primes 8 ∧ primes 8 ≤ 2503 ∧
    Row (primes 8) (states 8) (states 9) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
