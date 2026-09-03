import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_148 : 3 ≤ primes 148 ∧ primes 148 ≤ 2503 ∧
    Row (primes 148) (states 148) (states 149) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
