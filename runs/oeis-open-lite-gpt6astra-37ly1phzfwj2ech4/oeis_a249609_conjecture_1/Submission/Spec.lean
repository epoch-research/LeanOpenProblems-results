import FormalConjectures.Util.ProblemImports

open Nat List

/--
A249609: $a(n)$ is the smallest $m$, $1 \le m \le n$, such that $\binom{n}{m}$ is evil (A001969); $a(n)=0$ if there is no such $m$.
An evil number is one whose population count (number of set bits in binary) is even.
-/
def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  sorry

theorem oeis_a249609_conjecture_1.disproof : ¬ (type_of% @oeis_a249609_conjecture_1) := sorry
