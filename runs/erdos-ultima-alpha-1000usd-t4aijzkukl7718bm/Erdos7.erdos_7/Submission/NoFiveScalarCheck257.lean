import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_257 : 3 ≤ primes 257 ∧ primes 257 ≤ 2503 ∧
    Row (primes 257) (states 257) (states 258) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
