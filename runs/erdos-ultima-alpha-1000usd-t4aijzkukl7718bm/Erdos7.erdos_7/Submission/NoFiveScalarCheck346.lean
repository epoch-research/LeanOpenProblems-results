import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_346 : 3 ≤ primes 346 ∧ primes 346 ≤ 2503 ∧
    Row (primes 346) (states 346) (states 347) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
