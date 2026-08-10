import FormalConjectures.Util.ProblemImports
partial def badSub (n : ℕ) : {m : ℕ // m = n} := badSub n
example (n : ℕ) : ∃ m, m = n := ⟨(badSub n).1, (badSub n).2⟩
#print axioms badSub
