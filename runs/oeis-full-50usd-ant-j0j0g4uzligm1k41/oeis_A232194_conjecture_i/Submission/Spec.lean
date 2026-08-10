import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 100000

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
by
  refine ⟨?_, ?_, ?_⟩
  · -- (i.a) a(n) > 0 for n > 2.
    -- This asserts that for every n > 2 there is x ∈ [1, n-1] with both linear forms
    -- (n-1)x + n  and  n² - (n+1)x  prime. This is a special case of Dickson's
    -- conjecture / the Hardy–Littlewood prime k-tuple conjecture, which is open
    -- (blocked by the parity problem; at least as hard as the twin prime conjecture).
    intro hn
    sorry
  · -- (i.b, forward) a(n) = 1 → n ∈ {3,4,6,20,24}.
    -- Equivalently a(n) ≥ 2 for all n > 24, again an open simultaneous-primality
    -- existence statement.
    intro h
    sorry
  · -- (i.b, backward) the five exceptional values each give exactly a(n) = 1.
    -- This finite part is rigorously verified.
    rintro (rfl | rfl | rfl | rfl | rfl) <;> decide
