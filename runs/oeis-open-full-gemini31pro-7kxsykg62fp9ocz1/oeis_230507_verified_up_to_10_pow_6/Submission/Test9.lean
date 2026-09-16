import Submission.Spec
open OeisA230507

-- 2 * 2^4 - 1 = 31
-- 2 * 100^4 - 1 = 199999999
-- Let's test a large one
theorem test_prime_large : Nat.Prime 1249 := by norm_num
