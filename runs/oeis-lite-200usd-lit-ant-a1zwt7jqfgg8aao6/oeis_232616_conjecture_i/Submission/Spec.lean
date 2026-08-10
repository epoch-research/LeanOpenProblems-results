import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have hn : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).

The proof below reduces the conjecture to its irreducible mathematical core:
since `A232616 n = sInf {m | A232616_prop n m}` and `sInf` is a lower bound for
any member of the set, it suffices to exhibit a single value `m < 2*(prime(n)-1)`
for which `A232616_prop n m` holds, i.e. for which the first `m` values of
`2^k - k (mod n)` already form a complete residue system.  Taking `m = b - 1`
with `b = 2*(prime(n)-1)` (the largest admissible value), the whole conjecture
is equivalent to the single covering statement `A232616_prop n (b - 1)`.
-/
theorem oeis_232616_conjecture_i (n : ℕ) (hn : 0 < n) :
    A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  have hn0 : n ≠ 0 := hn.ne'
  haveI : NeZero n := ⟨hn0⟩
  -- The `n`-th prime is at least `2`, hence the bound `b` is positive.
  have hp : 2 ≤ Nat.nth Nat.Prime (n - 1) := (Nat.prime_nth_prime _).two_le
  set b := 2 * (Nat.nth Nat.Prime (n - 1) - 1) with hb
  have hb1 : 1 ≤ b := by omega
  -- Core covering bound: by `m = b - 1 = 2*(prime(n)-1) - 1` the set
  -- `{2^k - k (mod n) : 1 ≤ k ≤ m}` is already a complete residue system mod `n`.
  -- This is the content of Sun's (open) conjecture A232616(i).
  have hcov : A232616_prop n (b - 1) := by sorry
  -- `sInf` of the witnessing set is bounded above by the witness `b - 1`.
  have hle : A232616 n ≤ b - 1 := by
    unfold A232616
    rw [dif_neg hn0]
    exact Nat.sInf_le hcov
  omega
