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
lemma squarefree_four : squarefreePart 4 = 1 := by
  apply squarefreePart_of_isSquare
  use 2

lemma square_four : squarePart 4 = 4 := by
  dsimp [squarePart]
  rw [squarefree_four]

lemma a089026_four : a089026 4 = 2 := by
  dsimp [a089026]
  rw [square_four]
  have h := Nat.sqrt_eq 2
  exact h

lemma a_three_eq_fortynine : a 3 = 49 := by
  dsimp [a]
  rw [(Finset.Ico_succ_right_eq_Icc 1 3).symm]
  change (∑ k ∈ Ico (1 : ℕ) (3 + 1 : ℕ), (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs = 49
  have h3 : 1 ≤ 3 := by decide
  rw [Finset.sum_Ico_succ_top h3]
  have h2 : 1 ≤ 2 := by decide
  rw [Finset.sum_Ico_succ_top h2]
  have h1 : 1 ≤ 1 := by decide
  rw [Finset.sum_Ico_succ_top h1]
  rw [Finset.Ico_self]
  rw [Finset.sum_empty]
  norm_num

theorem a007406_conjecture_0.disproof : ¬ ∀ (n : ℕ) (hn : n > 3), Nat.gcd n (a (n - 1)) = a089026 n := by
  intro h
  have h4 : 4 > 3 := by decide
  have h_spec := h 4 h4
  rw [a_three_eq_fortynine, a089026_four] at h_spec
  revert h_spec
  decide
