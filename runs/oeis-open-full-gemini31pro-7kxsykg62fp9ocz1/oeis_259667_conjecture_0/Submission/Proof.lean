import Submission.Spec
import Mathlib

open Nat

theorem C_n_odd (n : ℕ) : (catalan n) % 2 = 1 ↔ n = 2^(Nat.log2 (n + 1)) - 1 := sorry

-- Wait, the conjecture is A259667 (2^k - 1) = 3 for all k > 8
-- But 3 % 2 = 1. The Catalan number is odd iff n = 2^k - 1.
-- So we know A259667 (2^k - 1) is odd. Thus it is 1, 3, or 5.

-- We also need to show that A259667 (2^k - 1) = 3 means (catalan n) % 3 = 0.
-- By Kummer's theorem, v_3(catalan n) is the number of carries when adding n and n in base 3, minus v_3(n+1).
-- Since n = 2^k - 1, n+1 = 2^k, so v_3(n+1) = 0.
-- Thus v_3(catalan n) = carries in base 3 of n + n.
-- The number of carries is 0 iff n has no digit 2 in base 3.
-- So catalan (2^k - 1) % 3 ≠ 0 iff 2^k - 1 has no digit 2 in base 3.

-- The conjecture is that 2^k - 1 has no digit 2 in base 3 only for k = 0, 1, 2, 5, 8.
-- So for k > 8, it always has a digit 2, hence v_3 > 0, so catalan n % 3 = 0.
-- Combined with catalan n % 2 = 1, we get catalan n % 6 = 3.

-- So the conjecture is equivalent to: "2^k - 1 has no digit 2 in base 3 only for k = 0, 1, 2, 5, 8."
-- This is a well-known open problem! It was conjectured by Erdős, or something similar.
-- Or maybe it's related to the ternary expansion of 2^k.
