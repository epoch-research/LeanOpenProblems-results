import FormalConjectures.Util.ProblemImports
import Submission.TestCertFinal

set_option maxRecDepth 2000000
set_option exponentiation.threshold 1000000

theorem hN_proof : my_N_val = R.my_M - 1 := by decide
