import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_210 : 3 ≤ primes 210 ∧ primes 210 ≤ 2503 ∧
    Row (primes 210) (states 210) (states 211) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
