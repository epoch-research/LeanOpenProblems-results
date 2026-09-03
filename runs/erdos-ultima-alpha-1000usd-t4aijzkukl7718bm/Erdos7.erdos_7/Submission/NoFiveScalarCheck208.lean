import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_208 : 3 ≤ primes 208 ∧ primes 208 ≤ 2503 ∧
    Row (primes 208) (states 208) (states 209) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
