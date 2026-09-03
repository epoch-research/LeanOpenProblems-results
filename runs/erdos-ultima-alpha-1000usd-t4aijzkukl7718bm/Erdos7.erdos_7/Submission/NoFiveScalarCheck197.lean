import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_197 : 3 ≤ primes 197 ∧ primes 197 ≤ 2503 ∧
    Row (primes 197) (states 197) (states 198) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
