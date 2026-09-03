import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_242 : 3 ≤ primes 242 ∧ primes 242 ≤ 2503 ∧
    Row (primes 242) (states 242) (states 243) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
