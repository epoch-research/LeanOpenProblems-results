import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_216 : 3 ≤ primes 216 ∧ primes 216 ≤ 2503 ∧
    Row (primes 216) (states 216) (states 217) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
