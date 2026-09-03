import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_40 : 3 ≤ primes 40 ∧ primes 40 ≤ 2503 ∧
    Row (primes 40) (states 40) (states 41) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
