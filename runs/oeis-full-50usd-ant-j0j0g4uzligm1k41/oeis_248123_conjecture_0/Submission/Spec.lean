import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A248123: Least integer $m > 0$ such that $\gcd(m,n) = 1$ and $m \cdot n \mid C(m+n)$,
where $C(k)$ refers to the $k$-th Catalan number $\binom{2k}{k}/(k+1)$.
-/
noncomputable def A248123 (n : ℕ) : ℕ :=
  -- Define the $k$-th Catalan number $C(k)$ explicitly.
  let catalan (k : ℕ) : ℕ := (2 * k).choose k / (k + 1)

  -- The sequence value a(n) is the least element (infimum) of the set of candidates.
  sInf {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n)}

/-- A248123 Conjecture: a(n) exists for all n > 0.

Since `A248123 n = sInf S` where
`S = {m | m > 0 ∧ gcd m n = 1 ∧ (m*n) ∣ C(m+n)}`, and every element of `S` is
positive, we have `A248123 n > 0` iff `S` is nonempty (because `Nat.sInf` of a
nonempty set of naturals is a member of the set, while `Nat.sInf ∅ = 0`).  Thus
the conjecture is equivalent to: for every `n > 0` there exists `m > 0` coprime to
`n` with `m * n ∣ C(m+n)`.  The reduction below is rigorous; the remaining
`Nonempty` goal is the genuine content of the conjecture. -/
theorem oeis_248123_conjecture_0 (n : ℕ) (hn : n > 0) : A248123 n > 0 := by
  have key : {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧
      (m * n) ∣ ((2 * (m + n)).choose (m + n) / (m + n + 1))}.Nonempty := by
    sorry
  exact (Nat.sInf_mem key).1
