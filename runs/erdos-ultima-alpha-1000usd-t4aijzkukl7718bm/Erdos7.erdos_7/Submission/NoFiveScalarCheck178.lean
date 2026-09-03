import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_178 : 3 ≤ primes 178 ∧ primes 178 ≤ 2503 ∧
    Row (primes 178) (states 178) (states 179) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
