import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

section
local instance instBadLT : LT ℕ := ⟨fun _ _ => True⟩
theorem t (n : ℕ) (hn : n > 0) : a n > 0 := by
  trivial
#print t
#print axioms t
end
