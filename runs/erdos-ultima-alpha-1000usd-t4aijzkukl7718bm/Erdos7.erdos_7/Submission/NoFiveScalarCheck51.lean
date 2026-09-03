import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_51 : 3 ≤ primes 51 ∧ primes 51 ≤ 2503 ∧
    Row (primes 51) (states 51) (states 52) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
