import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_226 : 3 ≤ primes 226 ∧ primes 226 ≤ 2503 ∧
    Row (primes 226) (states 226) (states 227) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
