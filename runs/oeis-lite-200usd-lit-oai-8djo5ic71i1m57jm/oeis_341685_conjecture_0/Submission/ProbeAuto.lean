import FormalConjectures.Util.ProblemImports
open Nat BigOperators Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#synth Fact False
#synth Finite (Padic 3)
#synth Subsingleton (Padic 3)
#synth Fintype (Padic 3)
#synth IsEmpty (Padic 3)
#synth Fact (IsAlgebraic ℚ (xi_3))
#synth Fact (¬ IsAlgebraic ℚ (xi_3))
#check false_of_nontrivial_of_subsingleton (Padic 3)
#check Fintype.false (α := Padic 3)
#check Infinite.false (α := Padic 3)
#check Finite.false (α := Padic 3)
#check not_preirreducible_nontrivial_t2 (Padic 3)
#synth PreirreducibleSpace (Padic 3)
#check IsAlgebraic.of_finite (A := ℚ) (B := Padic 3)
#check Algebra.IsAlgebraic.of_finite (R := ℚ) (A := Padic 3)
#check Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := Padic 3)
#check Algebra.IsAlgebraic.isAlgebraic_iff (R := ℚ) (A := Padic 3)
#check Algebra.IsAlgebraic.isAlgebraic_iff_top (R := ℚ) (A := Padic 3)
#check Algebra.IsAlgebraic.isAlgebraic_iff_bot (R := ℚ) (A := Padic 3)
