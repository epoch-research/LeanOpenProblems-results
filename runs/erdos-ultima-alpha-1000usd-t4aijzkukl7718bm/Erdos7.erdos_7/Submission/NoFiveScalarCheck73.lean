import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_73 : 3 ≤ primes 73 ∧ primes 73 ≤ 2503 ∧
    Row (primes 73) (states 73) (states 74) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
