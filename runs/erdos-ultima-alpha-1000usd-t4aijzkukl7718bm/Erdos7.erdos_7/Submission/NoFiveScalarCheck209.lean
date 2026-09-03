import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_209 : 3 ≤ primes 209 ∧ primes 209 ≤ 2503 ∧
    Row (primes 209) (states 209) (states 210) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
