import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

axiom fakeFinite : Module.Finite ℚ (Padic 3)

example : IsAlgebraic ℚ xi_3 := by
  haveI := fakeFinite
  exact IsAlgebraic.of_finite ℚ xi_3

#print axioms _root_.fakeFinite
