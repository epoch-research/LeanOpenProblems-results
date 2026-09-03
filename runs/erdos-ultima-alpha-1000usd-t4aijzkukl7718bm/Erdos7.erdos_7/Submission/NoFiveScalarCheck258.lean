import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_258 : 3 ≤ primes 258 ∧ primes 258 ≤ 2503 ∧
    Row (primes 258) (states 258) (states 259) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
