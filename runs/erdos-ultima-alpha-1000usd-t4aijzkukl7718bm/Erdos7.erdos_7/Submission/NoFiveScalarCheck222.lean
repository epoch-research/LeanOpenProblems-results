import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_222 : 3 ≤ primes 222 ∧ primes 222 ≤ 2503 ∧
    Row (primes 222) (states 222) (states 223) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
