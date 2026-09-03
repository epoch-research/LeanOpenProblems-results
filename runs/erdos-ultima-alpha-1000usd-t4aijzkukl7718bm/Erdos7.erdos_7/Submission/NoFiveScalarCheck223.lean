import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_223 : 3 ≤ primes 223 ∧ primes 223 ≤ 2503 ∧
    Row (primes 223) (states 223) (states 224) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
