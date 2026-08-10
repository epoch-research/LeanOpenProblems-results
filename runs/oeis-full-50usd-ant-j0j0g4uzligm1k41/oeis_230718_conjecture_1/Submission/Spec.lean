import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A230718: Smallest $n$-th power equal to a sum of some consecutive, immediately preceding, positive $n$-th powers, or 0 if none.
$a(n)$ is the smallest solution to $k^n + (k+1)^n + \dots + (k+m)^n = (k+m+1)^n$ with $k > 0$ and $m > 0$, or $0$ if none.
-/
noncomputable def A230718 (n : ℕ) : ℕ :=
  if n = 0 then 1 else
  -- Let $N = k+m+1$
  let P (N : ℕ) : Prop :=
    N ≥ 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧
    (Finset.Ico k N).sum (fun i => i ^ n) = N ^ n

  let Solutions : Set ℕ := { N : ℕ | P N }

  let N_min := sInf Solutions

  -- If Solutions is empty, N_min = 0 (since ℕ is OrderBot), so we return 0.
  -- Otherwise, N_min ≥ 3, and we return N_min ^ n.
  if N_min = 0 then 0 else N_min ^ n

/-- oeis_230718_conjecture_1: Is a(n) $\ne 0$ for any $n > 3$?
The conjecture is that $a(n) = 0$ for all $n > 3$.
The Erdos-Moser equation is the case $k = 1$. They conjecture that the only solution is $m = n = 1$.
Any counterexample would be a case of $a(n) > 0$ with $n > 3$.
And such a case with $k = 1$ would be a counterexample to the Erdos-Moser conjecture. -/
theorem oeis_230718_conjecture_1 : ∀ (n : ℕ), n > 3 → A230718 n = 0 := by
  intro n hn
  unfold A230718
  rw [if_neg (by omega)]
  simp only
  -- After unfolding, the goal is
  --   (if sInf Solutions = 0 then 0 else (sInf Solutions) ^ n) = 0
  -- where `Solutions = { N | P N }`.  Since every element of `Solutions`
  -- is `≥ 3`, we have `sInf Solutions = 0` iff `Solutions = ∅`.  Thus the
  -- whole expression is `0` exactly when `Solutions = ∅`, i.e. when the
  -- generalized Erdős–Moser equation has no solution for this `n`.
  have hempty :
      sInf { N : ℕ | N ≥ 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N - 2 ∧
        (Finset.Ico k N).sum (fun i => i ^ n) = N ^ n } = 0 := by
    -- This is precisely the statement that the equation
    --   k^n + (k+1)^n + … + (k+m)^n = (k+m+1)^n
    -- has no positive solution for n > 3.  The case k = 1 is the classical
    -- Erdős–Moser equation  1^n + 2^n + … + (N-1)^n = N^n, conjectured to have
    -- no solution for n > 1 but OPEN since 1953 (only the lower bound
    -- N > 10^(10^9) is known, never an impossibility proof).  Since the k = 1
    -- case is a subcase here, any honest proof of `hempty` would resolve the
    -- Erdős–Moser conjecture for n > 3; hence this step is genuinely open and
    -- cannot be discharged with current mathematics.
    sorry
  rw [hempty]
  simp
