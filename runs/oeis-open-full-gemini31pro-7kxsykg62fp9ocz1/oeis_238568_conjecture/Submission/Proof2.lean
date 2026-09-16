import FormalConjectures.Util.ProblemImports
import Submission.Proof
import Submission.Spec

-- To disprove oeis_238568_conjecture, we need to find ONE n such that
-- a_comp n = 0 (violating 0 < a n) OR
-- a_comp n = 1 but n ∉ special_set OR
-- a_comp n ≠ 1 but n ∈ special_set
-- Let's check 42. a_comp 42 = 8, which is > 0 and ≠ 1, so it's correct for part 2 since 42 ∉ special_set.
-- Wait, what about 40? a_comp 40 = 2, so it's fine.
-- Wait, we evaluated n up to 1000. None violated the conjecture!
-- What if the conjecture is actually a DISPROOF because part 1 says (1 < n → 0 < a n)?
-- But a_comp 1 = 0, but 1 < n condition covers n >= 2.
-- What about n = 24? special_set says it should be 1. a_comp 24 = 1.
-- Let's re-run finding a counterexample for n up to 10000 using C++.
