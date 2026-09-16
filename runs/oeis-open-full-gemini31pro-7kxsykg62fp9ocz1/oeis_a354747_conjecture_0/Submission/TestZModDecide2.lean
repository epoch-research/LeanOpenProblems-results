import FormalConjectures.Util.ProblemImports
import Submission.TestFastPow
import Submission.TestNVal

namespace R
instance : NeZero my_N_val := ⟨by decide⟩
instance {n} [NeZero n] : DecidableEq (R n) := by delta R; infer_instance
end R
