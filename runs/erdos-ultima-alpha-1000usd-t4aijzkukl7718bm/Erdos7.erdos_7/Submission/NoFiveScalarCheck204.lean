import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_204 : 3 ≤ primes 204 ∧ primes 204 ≤ 2503 ∧
    Row (primes 204) (states 204) (states 205) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
