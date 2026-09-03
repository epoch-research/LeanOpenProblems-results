import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_218 : 3 ≤ primes 218 ∧ primes 218 ≤ 2503 ∧
    Row (primes 218) (states 218) (states 219) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
