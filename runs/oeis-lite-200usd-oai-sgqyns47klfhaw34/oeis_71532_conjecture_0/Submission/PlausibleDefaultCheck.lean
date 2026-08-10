import FormalConjectures.Util.ProblemImports
open Plausible
#reduce (default : TestResult False)
#check TestResult.noConfusion
#check TestResult.rec
example : (default : TestResult False) = TestResult.success (PSum.inl ()) := by rfl
-- Can noConfusion yield arbitrary P from bogus equality? no equality.
