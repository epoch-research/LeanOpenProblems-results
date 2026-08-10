import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
example : xi_3 ∈ algebraicClosure ℚ (Padic 3) := by
  simp [algebraicClosure]
example : IsAlgebraic ℚ xi_3 := by
  exact (mem_algebraicClosure_iff.mp (by simp [algebraicClosure] : xi_3 ∈ algebraicClosure ℚ (Padic 3)))
#print axioms _example
