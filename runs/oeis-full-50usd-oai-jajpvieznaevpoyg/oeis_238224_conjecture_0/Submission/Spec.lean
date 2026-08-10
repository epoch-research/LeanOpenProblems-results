import FormalConjectures.Util.ProblemImports

open Nat

/--
A238224: Number of pairs $\{j, k\}$ with $0 < j < k \le n$ and $k \equiv 1 \pmod j$
such that $\pi(j \cdot n)$ divides $\pi(k \cdot n)$, where $\pi(\cdot)$ is the prime counting function ($\pi = \text{primeCounting}$).
-/
noncomputable def A238224 (n : ℕ) : ℕ :=
  -- Iterate j over {1, 2, ..., n-1}.
  Finset.sum (Finset.Ico 1 n) fun j =>
    -- The upper limit for q comes from k = j*q + 1 $\le$ n, which implies q $\le$ (n - 1) / j.
    let upper_q : ℕ := (n - 1) / j
    -- Iterate q over {1, 2, ..., upper_q}. This ensures k = j*q + 1 is a valid term.
    Finset.sum (Finset.Icc 1 upper_q) fun q =>
      let k := j * q + 1
      -- The condition: pi(j*n) divides pi(k*n).
      if Nat.primeCounting (j * n) ∣ Nat.primeCounting (k * n) then 1 else 0

/--
%C A238224 Conjecture: a(n) > 0 for all n > 1.
-/
theorem oeis_238224_conjecture_0 : ∀ n : ℕ, 1 < n → A238224 n > 0 := by
  sorry
