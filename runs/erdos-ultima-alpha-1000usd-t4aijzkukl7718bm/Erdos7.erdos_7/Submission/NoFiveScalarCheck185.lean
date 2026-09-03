import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_185 : 3 ≤ primes 185 ∧ primes 185 ≤ 2503 ∧
    Row (primes 185) (states 185) (states 186) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
