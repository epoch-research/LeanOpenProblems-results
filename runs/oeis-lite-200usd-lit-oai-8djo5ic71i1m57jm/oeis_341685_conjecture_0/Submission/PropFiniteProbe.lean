import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#synth Finite (IsAlgebraic ℚ xi_3)
#synth Decidable (IsAlgebraic ℚ xi_3)
#synth Subsingleton (IsAlgebraic ℚ xi_3)
#synth Fintype (IsAlgebraic ℚ xi_3)
#synth Nonempty (Decidable (IsAlgebraic ℚ xi_3))
#synth Inhabited (Decidable (IsAlgebraic ℚ xi_3))
#check Finite.exists_equiv_fin
#check Fintype.equivFin
#check Finite.exists_equiv_fin (IsAlgebraic ℚ xi_3)
example : IsAlgebraic ℚ xi_3 := by
  classical
  haveI : Fintype (IsAlgebraic ℚ xi_3) := Fintype.ofFinite _
  -- no element if empty
  exact?
