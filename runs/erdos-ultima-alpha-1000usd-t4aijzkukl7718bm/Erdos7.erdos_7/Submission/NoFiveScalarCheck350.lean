import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_350 : 3 ≤ primes 350 ∧ primes 350 ≤ 2503 ∧
    Row (primes 350) (states 350) (states 351) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
