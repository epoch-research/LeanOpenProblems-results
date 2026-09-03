import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_48 : 3 ≤ primes 48 ∧ primes 48 ≤ 2503 ∧
    Row (primes 48) (states 48) (states 49) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
