import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

mutual
partial def pf (n : ℕ) (hn : n > 0) : a n > 0 :=
  (nepf n hn).some
partial def nepf (n : ℕ) (hn : n > 0) : Nonempty (a n > 0) :=
  ⟨pf n hn⟩
end

#print axioms pf
#print axioms nepf
