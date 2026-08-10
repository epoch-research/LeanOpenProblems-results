import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#synth Field (Padic 3)
#synth Algebra ℚ (Padic 3)
#synth Module ℚ (Padic 3)
#synth Module.IsTorsionFree ℚ (Padic 3)
#synth FaithfulSMul ℚ (Padic 3)
#synth CharZero (Padic 3)
#synth Infinite (Padic 3)
#synth Nontrivial (Padic 3)
#synth CompleteSpace (Padic 3)
#synth SeparatedSpace (Padic 3)
#synth T2Space (Padic 3)
#synth TotallyDisconnectedSpace (Padic 3)
#synth TotallySeparatedSpace (Padic 3)
#synth IsAlgClosure ℚ (Padic 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)
#synth Module.Finite ℚ (Padic 3)
#synth FiniteDimensional ℚ (Padic 3)
#synth Subsingleton (Padic 3)
#synth Countable (Padic 3)
#synth Fintype (Padic 3)
#synth Finite (Padic 3)
#synth Algebra.IsIntegral ℚ (Padic 3)

example : IsAlgebraic ℚ xi_3 := by
  exact IsAlgebraic.of_finite ℚ xi_3
