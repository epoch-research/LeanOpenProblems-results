import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_189 : 3 ≤ primes 189 ∧ primes 189 ≤ 2503 ∧
    Row (primes 189) (states 189) (states 190) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
