import FormalConjectures.Util.ProblemImports

open Finset Rat Int Nat

/--
A007406: Wolstenholme numbers: numerator of $\sum_{k=1}^n \frac{1}{k^2}$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun k : ℕ => (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs

/--
A089026: Largest $k$ such that $k^2$ divides $n$. Equivalently, $\sqrt{\text{largest square factor of } n}$.
This is $\sqrt{\text{Nat.squarePart } n}$.
We define this using `Nat.sqrt` of `Nat.squarePart`, which is the largest square factor.
-/
def a089026 (n : ℕ) : ℕ :=
  Nat.sqrt n.squarePart

/--
%C A007406 Conjecture: for n > 3, gcd(n, a(n-1)) = A089026(n).
-/
theorem a007406_conjecture_0.disproof :
    ¬ ∀ (n : ℕ) (hn : n > 3), Nat.gcd n (a (n - 1)) = a089026 n := by
  intro h
  have hbad : Nat.gcd 4 (a (4 - 1)) ≠ a089026 4 := by
    rw [show 4 - 1 = 3 by norm_num]
    rw [show a 3 = 49 by norm_num [a, Finset.sum_Icc_succ_top]]
    rw [show a089026 4 = 2 by
      rw [a089026, Nat.squarePart, Nat.squarefreePart_of_isSquare (by use 2)]
      norm_num]
    norm_num
  exact hbad (h 4 (by norm_num))
