import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Predicate for $m \in \mathbb{N}$ to be of the form $w(3w+1)/2$ for some $w \in \mathbb{Z}$.
This is equivalent to $24m+1$ being a perfect square. Returns a Boolean value.
-/
def is_A271026_w_term (R : ℕ) : Bool :=
  (Nat.sqrt (24 * R + 1)) ^ 2 = 24 * R + 1

/--
A271026: Number of ordered ways to write $n$ as $x^7 + y^4 + z^3 + w(3w+1)/2$,
where $x, y, z$ are nonnegative integers, and $w$ is an integer.
-/
def A271026 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun x =>
  if x^7 > n then 0 else
  Finset.sum (Finset.range (n + 1)) fun y =>
    if x^7 + y^4 > n then 0 else
    Finset.sum (Finset.range (n + 1)) fun z =>
      let S := x^7 + y^4 + z^3
      if S > n then 0 else
      let R := n - S
      if is_A271026_w_term R then 1 else 0

/-- The set of natural numbers $n$ for which $A271026(n) = 1, as conjectured. -/
def A271026_unique_set : Finset ℕ :=
  {0, 47, 61, 62, 112, 175, 448, 573, 714, 1073, 1175, 1839, 2167, 8043, 13844}

/--
Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 47, 61, 62, 112, 175, 448, 573, 714, 1073, 1175, 1839, 2167, 8043, 13844.
-/
theorem oeis_271026_conjecture_0 :
  (∀ (n : ℕ), A271026 n > 0) ∧
  (∀ (n : ℕ), A271026 n = 1 ↔ n ∈ A271026_unique_set) :=
by sorry
