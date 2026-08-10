import FormalConjectures.Util.ProblemImports

open Nat

-- Experimental: prove the p-adic inequality suggested by computation.
-- For p ≤ n^3 - n, the p-adic valuation of choose(n^3,n) is at most that of (n^3-n)!.
example {n p : ℕ} (hn : 14 ≤ n) (hp : p.Prime) (hle : p ≤ n ^ 3 - n) :
    (Nat.choose (n ^ 3) n).factorization p ≤ ((n ^ 3 - n)!).factorization p := by
  -- Use Kummer/Legendre formulas.  It suffices to bound the number of carries by v_p((N-n)!).
  rw [Nat.factorization_choose hp (by
    -- n ≤ n^3
    have hnpos : 0 < n := by omega
    calc n = n * 1 := by rw [mul_one]
      _ ≤ n * (n * n) := Nat.mul_le_mul_left n (by nlinarith [hnpos])
      _ = n ^ 3 := by ring) (Nat.lt_add_one _)]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one _)]
  -- Goal: cardinality of a subset of Ico 1 (log p n^3 +1) ≤ sum over Ico 1 (log p (n^3-n)+1) of floor((n^3-n)/p^i).
  -- Since p ≤ n^3-n, the i=1 term is at least 1; but cardinality may be up to log_p(n^3), around 3 log_p n.
  -- factorial valuation is huge for small p; for p near N-n, cardinality at most 1.
  -- Need a split proof. Automation won't solve it.
  sorry
