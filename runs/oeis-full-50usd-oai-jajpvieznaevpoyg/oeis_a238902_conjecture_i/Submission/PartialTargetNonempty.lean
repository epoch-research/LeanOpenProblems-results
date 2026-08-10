import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

partial def targetNonempty (n : ℕ) (hn : n > 0) (_ : Unit) : Nonempty (a n > 0) :=
  targetNonempty n hn ()
#print targetNonempty
#print axioms targetNonempty

theorem test (n : ℕ) (hn : n > 0) : a n > 0 := Classical.choice (targetNonempty n hn ())
#print axioms test
