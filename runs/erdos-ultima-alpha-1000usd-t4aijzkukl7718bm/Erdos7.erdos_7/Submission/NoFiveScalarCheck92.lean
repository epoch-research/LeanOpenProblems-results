import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_92 : 3 ≤ primes 92 ∧ primes 92 ≤ 2503 ∧
    Row (primes 92) (states 92) (states 93) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
