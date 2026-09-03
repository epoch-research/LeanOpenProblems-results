import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_301 : 3 ≤ primes 301 ∧ primes 301 ≤ 2503 ∧
    Row (primes 301) (states 301) (states 302) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
