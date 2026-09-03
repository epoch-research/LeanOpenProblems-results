import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_205 : 3 ≤ primes 205 ∧ primes 205 ≤ 2503 ∧
    Row (primes 205) (states 205) (states 206) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
