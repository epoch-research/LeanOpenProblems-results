import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_27 : 3 ≤ primes 27 ∧ primes 27 ≤ 2503 ∧
    Row (primes 27) (states 27) (states 28) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
