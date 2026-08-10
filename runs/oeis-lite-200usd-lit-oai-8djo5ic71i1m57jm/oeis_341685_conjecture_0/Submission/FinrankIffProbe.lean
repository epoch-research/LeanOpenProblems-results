import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Module.finrank_pos_iff_exists_ne_zero
#check Module.finrank_pos_iff
#check Module.finite_of_finrank_pos
#synth Module.Free ℚ (Padic 3)
example : Module.Finite ℚ (Padic 3) := by
  have hpos : 0 < Module.finrank ℚ (Padic 3) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨(1 : Padic 3), one_ne_zero⟩
  exact Module.finite_of_finrank_pos hpos
