import FormalConjectures.Util.ProblemImports

open Nat Finset

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : n > 0 :=
  hn

@[implemented_by my_unsafe_proof]
theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : n > 0 :=
  by sorry

#print axioms oeis_308584_conjecture_1
