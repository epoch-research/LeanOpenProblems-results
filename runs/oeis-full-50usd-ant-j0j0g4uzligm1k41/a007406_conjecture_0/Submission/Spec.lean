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

This conjecture is FALSE under the formalized definitions of `a` and `a089026`.
The very first relevant case `n = 4` is already a counterexample:
`a 3 = 49` (numerator of `1 + 1/4 + 1/9 = 49/36`), so `gcd 4 (a 3) = gcd 4 49 = 1`,
whereas `a089026 4 = Nat.sqrt (squarePart 4) = Nat.sqrt 4 = 2`, and `1 ≠ 2`.
-/
theorem a007406_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), n > 3 → Nat.gcd n (a (n - 1)) = a089026 n := by
  intro h
  have h4 := h 4 (by norm_num)
  -- Evaluate `a 3 = 49`.
  have ha : a (4 - 1) = 49 := by
    show a 3 = 49
    unfold a
    rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
  -- Evaluate `a089026 4 = 2`.
  have hb : a089026 4 = 2 := by
    unfold a089026 Nat.squarePart
    rw [Nat.squarefreePart_of_isSquare ⟨2, by norm_num⟩]
    norm_num
  rw [ha, hb] at h4
  -- Now `h4 : Nat.gcd 4 49 = 2`, which is false since `gcd 4 49 = 1`.
  norm_num at h4

