import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_16 : 3 ≤ primes 16 ∧ primes 16 ≤ 2503 ∧
    Row (primes 16) (states 16) (states 17) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
