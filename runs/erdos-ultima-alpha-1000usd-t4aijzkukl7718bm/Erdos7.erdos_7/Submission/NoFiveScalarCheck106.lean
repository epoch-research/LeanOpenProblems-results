import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_106 : 3 ≤ primes 106 ∧ primes 106 ≤ 2503 ∧
    Row (primes 106) (states 106) (states 107) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
