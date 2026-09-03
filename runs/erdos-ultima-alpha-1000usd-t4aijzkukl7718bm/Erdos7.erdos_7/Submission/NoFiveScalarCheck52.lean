import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_52 : 3 ≤ primes 52 ∧ primes 52 ≤ 2503 ∧
    Row (primes 52) (states 52) (states 53) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
