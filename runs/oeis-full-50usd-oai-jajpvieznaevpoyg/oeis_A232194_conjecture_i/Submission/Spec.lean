import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence A232194: Number of ways to write $n = x + y$ ($x, y > 0$) with $n x + y$ and $n y - x$ both prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    Nat.Prime (n * x + y) ∧ Nat.Prime (n * y - x)
  ) (Finset.Ico 1 n)

/--
Conjecture based on OEIS A232194 (i):
(i) a(n) > 0 for all n > 2. Also, a(n) = 1 only for n = 3, 4, 6, 20, 24.
-/
theorem oeis_A232194_conjecture_i (n : ℕ) :
  (n > 2 → a n > 0) ∧ (a n = 1 ↔ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24) :=
by sorry
