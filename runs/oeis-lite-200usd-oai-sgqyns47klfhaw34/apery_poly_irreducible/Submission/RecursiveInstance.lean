import FormalConjectures.Util.ProblemImports
open Nat Polynomial
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k
instance instFactIrred (n : ℕ) (hn : 1 ≤ n) : Fact (Irreducible (apery_poly n)) := ⟨(instFactIrred n hn).out⟩
example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := (instFactIrred n hn).out
#print axioms instFactIrred
