import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_241 : 3 ≤ primes 241 ∧ primes 241 ≤ 2503 ∧
    Row (primes 241) (states 241) (states 242) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
