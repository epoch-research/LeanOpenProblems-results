import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_194 : 3 ≤ primes 194 ∧ primes 194 ≤ 2503 ∧
    Row (primes 194) (states 194) (states 195) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
