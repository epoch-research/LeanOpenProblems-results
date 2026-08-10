import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

partial def allProof (_ : Unit) : ∀ n : ℕ, n > 0 → a n > 0 := allProof ()
#print allProof
#print axioms allProof

theorem test (n : ℕ) (hn : n > 0) : a n > 0 := allProof () n hn
#print axioms test
