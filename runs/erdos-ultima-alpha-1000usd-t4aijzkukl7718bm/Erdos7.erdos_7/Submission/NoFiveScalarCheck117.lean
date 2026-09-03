import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_117 : 3 ≤ primes 117 ∧ primes 117 ≤ 2503 ∧
    Row (primes 117) (states 117) (states 118) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
