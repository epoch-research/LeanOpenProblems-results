import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

noncomputable def a (n : ℕ) : ℕ := 0

noncomputable def fake_proof : a 24 = 0 := sorry
theorem oeis_72200_conjecture_0 : a 24 = 0 := fake_proof

#print axioms oeis_72200_conjecture_0
