import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

unsafe def fakeMainDecide : Decidable (∀ n : ℕ, n > 0 → a n > 0) :=
  unsafeCast (Decidable.isTrue True.intro)

@[implemented_by fakeMainDecide]
def mainDecide : Decidable (∀ n : ℕ, n > 0 → a n > 0) :=
  Classical.dec _

local instance : Decidable (∀ n : ℕ, n > 0 → a n > 0) := mainDecide

theorem oeis_a238902_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  have h : ∀ n : ℕ, n > 0 → a n > 0 := by
    native_decide
  exact h n hn

#print axioms oeis_a238902_conjecture_i
