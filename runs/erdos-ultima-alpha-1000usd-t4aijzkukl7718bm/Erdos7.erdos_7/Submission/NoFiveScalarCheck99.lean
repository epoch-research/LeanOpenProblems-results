import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_99 : 3 ≤ primes 99 ∧ primes 99 ≤ 2503 ∧
    Row (primes 99) (states 99) (states 100) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
