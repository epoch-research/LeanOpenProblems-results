import FormalConjectures.Util.ProblemImports
open Nat

def Good (n k : ℕ) : Prop := Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

partial def searchFrom (n k : ℕ) : {k // Good n k} :=
  if h : Good n k then ⟨k, h⟩ else searchFrom n (k+1)

example (n : ℕ) : ∃ k, Good n k := ⟨(searchFrom n 0).1, (searchFrom n 0).2⟩

#print axioms searchFrom
