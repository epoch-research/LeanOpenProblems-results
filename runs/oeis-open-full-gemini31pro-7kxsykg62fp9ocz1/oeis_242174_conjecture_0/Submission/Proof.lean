import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset Nat
open scoped Classical

-- Could there be an issue with `0 < n`?
-- What is `A242174 1`?
-- B(1) = 1^4 + 1^4 = 2.
-- `primeFactors B(1)` = {2}.
-- `Finset.Ico 1 1` is empty.
-- Filter condition `∀ k ∈ Ico 1 n, ¬(p ∣ B k)` is vacuously true.
-- So `A242174 1` is 2. 2 is prime.
-- For n=2, B(2) = 18. primeFactors = {2, 3}.
-- Ico 1 2 = {1}. B(1) = 2.
-- 2 divides B(1). So 2 is removed.
-- 3 does not divide B(1). So 3 is kept.
-- A242174 2 = 3. 3 is prime.
-- What about n=0? The conjecture says `∀ n : ℕ, 0 < n → (A242174 n).Prime`.
-- So n=0 is not checked.

-- Wait! Is the problem in the definition of `A_franel_r`?
-- `noncomputable def A_franel_r (r n : ℕ) : ℕ :=`
-- `  let B := franel_r r`
-- `  (B n).primeFactors.filter (fun p => ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)) |>.min.getD 1`
-- Wait! `A_franel_r r n` checks divisibility by `B k` for `k ∈ Ico 1 n`.
-- BUT what if `p` divides `B 0`?
-- `B 0 = 1`. No prime `p` divides 1. So it doesn't matter if we skip `k=0`.
-- This definition matches the A242174 one.

-- Could the problem be that the original A242174 conjecture actually says something else?
-- Z. W. Sun conjectured in 2014: "In general, for any r > 2, if n is large enough then f_r(n) has a prime divisor which does not divide any previous terms f_r(k) with k < n."
-- Wait! "with k < n"
-- The definition of A_franel_r checks `k ∈ Ico 1 n`.
-- This means `1 ≤ k < n`.
-- It DOES NOT check `k = 0`.
-- `B 0 = 1` for all r. So no prime divides `B 0`.
-- It DOES NOT check `k = 0`, but no prime divides `B 0 = 1` anyway!

-- WAIT. Look closely at A242174.
-- "Least prime divisor of A005260(n) which does not divide any previous term A005260(k) with k < n, or 1 if such a primitive prime divisor of A005260(n) does not exist."
-- For n=1, previous terms are k=0.
-- A005260(0) = 1.
-- So prime factors of A005260(1) = 2 are just 2.
-- 2 does not divide A005260(0) = 1.
-- So A242174(1) = 2.
-- Our Lean definition gives `Ico 1 n`, so for n=1 it checks NO previous terms. It also gives 2.

-- Wait, is it possible the conjecture is FALSE because `A242174` is NOT prime?
-- What if `min` is `none`? Then `getD 1` returns 1, which is not prime.
-- We searched up to 8000 for `r=4` and `min` was NEVER `none`.
