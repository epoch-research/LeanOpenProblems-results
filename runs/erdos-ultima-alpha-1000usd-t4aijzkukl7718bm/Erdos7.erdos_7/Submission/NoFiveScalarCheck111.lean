import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_111 : 3 ≤ primes 111 ∧ primes 111 ≤ 2503 ∧
    Row (primes 111) (states 111) (states 112) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
