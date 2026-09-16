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
theorem a007406_conjecture_0 (n : ℕ) (hn : n > 3) :
    Nat.gcd n (a (n - 1)) = a089026 n :=
  by sorry

lemma Icc_1_3 : Finset.Icc 1 3 = {1, 2, 3} := by rfl

lemma a_3 : a 3 = 49 := by
  unfold a
  rw [Icc_1_3]
  simp
  norm_num

lemma squarefreePart_4 : Nat.squarefreePart 4 = 1 := by
  apply Nat.squarefreePart_of_isSquare
  use 2

lemma a089026_4 : a089026 4 = 2 := by
  unfold a089026 Nat.squarePart
  rw [squarefreePart_4]
  norm_num

theorem a007406_conjecture_0.disproof : ¬ (type_of% @a007406_conjecture_0) := by
  intro h
  have h4 := h 4 (by decide)
  rw [a_3, a089026_4] at h4
  have h_gcd : Nat.gcd 4 49 = 1 := by decide
  rw [h_gcd] at h4
  contradiction
